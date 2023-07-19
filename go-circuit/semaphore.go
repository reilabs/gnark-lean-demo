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

// Example: Semaphore circuit with dummy Poseidon hash
type DummyPoseidon2 struct {
	In_1 frontend.Variable
	In_2 frontend.Variable
}

func (gadget DummyPoseidon2) DefineGadget(api abstractor.API) []frontend.Variable {
	hash := api.Mul(gadget.In_1, gadget.In_2)
	return []frontend.Variable{hash}
}

type DummyPoseidon1 struct {
	In frontend.Variable
}

func (gadget DummyPoseidon1) DefineGadget(api abstractor.API) []frontend.Variable {
	hash := api.Mul(gadget.In, gadget.In)
	return []frontend.Variable{hash}
}

type MerkleTreeInclusionProof struct {
	Leaf        frontend.Variable
	PathIndices []frontend.Variable
	Siblings    []frontend.Variable
}

func (gadget MerkleTreeInclusionProof) DefineGadget(api abstractor.API) []frontend.Variable {
	dummy_poseidon := api.DefineGadget(&DummyPoseidon2{})

	levels := len(gadget.PathIndices)
	hashes := make([]frontend.Variable, levels+1)

	hashes[0] = gadget.Leaf
	for i := 0; i < levels; i++ {
		// Unrolled merkle_tree_inclusion_proof
		api.AssertIsBoolean(gadget.PathIndices[i])
		leftHash := dummy_poseidon.Call(DummyPoseidon2{hashes[i], gadget.Siblings[i]})[0]
		rightHash := dummy_poseidon.Call(DummyPoseidon2{gadget.Siblings[i], hashes[i]})[0]
		hashes[i+1] = api.Select(gadget.PathIndices[i], rightHash, leftHash)
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

	// Working values
	Levels int
}

func (circuit *Semaphore) AbsDefine(api abstractor.API) error {
	// From https://github.com/semaphore-protocol/semaphore/blob/main/packages/circuits/semaphore.circom
	dummy_poseidon_1 := api.DefineGadget(&DummyPoseidon1{})
	dummy_poseidon_2 := api.DefineGadget(&DummyPoseidon2{})
	merkle_tree_inclusion_proof := api.DefineGadget(&MerkleTreeInclusionProof{
		PathIndices: make([]frontend.Variable, circuit.Levels),
		Siblings:    make([]frontend.Variable, circuit.Levels),
	})

	secret := dummy_poseidon_2.Call(DummyPoseidon2{circuit.IdentityNullifier, circuit.IdentityTrapdoor})[0]
	identity_commitment := dummy_poseidon_1.Call(DummyPoseidon1{secret})[0]
	nullifierHash := dummy_poseidon_2.Call(DummyPoseidon2{circuit.ExternalNullifier, circuit.IdentityNullifier})[0]
	api.AssertIsEqual(nullifierHash, circuit.NullifierHash) // Verify

	root := merkle_tree_inclusion_proof.Call(MerkleTreeInclusionProof{
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
