package main

import (
	"log"
	"os"
	"path/filepath"

	"github.com/reilabs/gnark-extractor/abstractor"
	"github.com/reilabs/gnark-extractor/extractor"

	"github.com/consensys/gnark-crypto/ecc"
	"github.com/consensys/gnark/frontend"

	"github.com/urfave/cli/v2"
)

type MerkleTreeRecoverRound struct {
	Direction frontend.Variable
	Hash      frontend.Variable
	Sibling   frontend.Variable
}

func (gadget MerkleTreeRecoverRound) DefineGadget(api abstractor.API) []frontend.Variable {
	api.AssertIsBoolean(gadget.Direction)
	leftHash := api.Call(Poseidon2{gadget.Hash, gadget.Sibling})[0]
	rightHash := api.Call(Poseidon2{gadget.Sibling, gadget.Hash})[0]
	parent_hash := api.Select(gadget.Direction, rightHash, leftHash)
	return []frontend.Variable{parent_hash}
}

type MerkleTreeInclusionProof struct {
	Leaf        frontend.Variable
	PathIndices []frontend.Variable
	Siblings    []frontend.Variable
}

func (gadget MerkleTreeInclusionProof) DefineGadget(api abstractor.API) []frontend.Variable {
	levels := len(gadget.PathIndices)
	hashes := make([]frontend.Variable, levels+1)

	hashes[0] = gadget.Leaf
	for i := 0; i < levels; i++ {
		hashes[i+1] = api.Call(MerkleTreeRecoverRound{gadget.PathIndices[i], hashes[i], gadget.Siblings[i]})[0]
	}
	root := hashes[levels]
	return []frontend.Variable{root}
}

type Semaphore struct {
	IdentityNullifier frontend.Variable   `gnark:",secret"`
	IdentityTrapdoor  frontend.Variable   `gnark:",secret"`
	TreePathIndices   []frontend.Variable `gnark:",secret"` // 0 | 1
	TreeSiblings      []frontend.Variable `gnark:",secret"`

	SignalHash        frontend.Variable `gnark:",public"`
	ExternalNullifier frontend.Variable `gnark:",public"`

	// Outputs to check
	NullifierHash frontend.Variable `gnark:",public"`
	MTRoot        frontend.Variable `gnark:",public"`

	// Parameters
	Levels int
}

func (circuit *Semaphore) AbsDefine(api abstractor.API) error {
	// From https://github.com/semaphore-protocol/semaphore/blob/main/packages/circuits/semaphore.circom

	secret := api.Call(Poseidon2{circuit.IdentityNullifier, circuit.IdentityTrapdoor})[0]
	identity_commitment := api.Call(Poseidon1{secret})[0]
	nullifierHash := api.Call(Poseidon2{circuit.ExternalNullifier, circuit.IdentityNullifier})[0]
	api.AssertIsEqual(nullifierHash, circuit.NullifierHash) // Verify

	root := api.Call(MerkleTreeInclusionProof{
		Leaf:        identity_commitment,
		PathIndices: circuit.TreePathIndices,
		Siblings:    circuit.TreeSiblings,
	})[0]

	api.AssertIsEqual(root, circuit.MTRoot) // Verify
	api.Mul(circuit.SignalHash, circuit.SignalHash)

	return nil
}

func (circuit Semaphore) Define(api frontend.API) error {
	return abstractor.Concretize(api, &circuit)
}

func TestSemaphore() (string, error) {
	nLevels := 3
	assignment := Semaphore{
		Levels:          nLevels,
		TreePathIndices: make([]frontend.Variable, nLevels),
		TreeSiblings:    make([]frontend.Variable, nLevels),
	}
	if len(assignment.TreePathIndices) != len(assignment.TreeSiblings) {
		panic("TreePathIndices and TreeSiblings must have the same length.")
	}
	return extractor.CircuitToLean(&assignment, ecc.BN254)
}

func main() {
	var out_file string

	app := &cli.App{
		Name:  "gnark-lean-demo",
		Usage: "gnark to lean circuit extractor",
		Commands: []*cli.Command{
			{
				Name:    "extract-circuit",
				Aliases: []string{"e"},
				Usage:   "Extract circuit to file",
				Flags: []cli.Flag{
					&cli.StringFlag{
						Name:        "out",
						Usage:       "Load configuration from `FILE`",
						Required:    true,
						Destination: &out_file,
					},
				},
				Action: func(cCtx *cli.Context) error {
					circuit_string, err := TestSemaphore()
					if err != nil {
						log.Fatal(err)
					}
					absPath, _ := filepath.Abs(out_file)
					err = os.MkdirAll(filepath.Dir(absPath), 0666)
					if err != nil && !os.IsExist(err) {
						log.Fatal(err)
					}
					err = os.WriteFile(absPath, []byte(circuit_string), 0666)
					if err != nil {
						log.Fatal(err)
					}
					return nil
				},
			},
		},
	}

	if err := app.Run(os.Args); err != nil {
		log.Fatal(err)
	}
}
