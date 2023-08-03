// Main shows how to use the library reilabs/gnark-lean-extractor by applying
// the Semaphore v3 circuit.
package main

import (
	"log"
	"os"
	"path/filepath"

	"github.com/reilabs/gnark-lean-extractor/abstractor"
	"github.com/reilabs/gnark-lean-extractor/extractor"

	"github.com/consensys/gnark-crypto/ecc"
	"github.com/consensys/gnark/frontend"

	"github.com/urfave/cli/v2"
)

// MerkleTreeRecoverRound is a gadget that calculates the parent hash in a MerkleTree
// given two children hashes (Hash and Sibling) and the direction
type MerkleTreeRecoverRound struct {
	Direction frontend.Variable
	Hash      frontend.Variable
	Sibling   frontend.Variable
}

func (gadget MerkleTreeRecoverRound) DefineGadget(api abstractor.API) []frontend.Variable {
	api.AssertIsBoolean(gadget.Direction)
	leftHash := api.Call(Poseidon2{gadget.Hash, gadget.Sibling})[0]
	rightHash := api.Call(Poseidon2{gadget.Sibling, gadget.Hash})[0]
	parentHash := api.Select(gadget.Direction, rightHash, leftHash)
	return []frontend.Variable{parentHash}
}

// MerkleTreeInclusionProof is a gadget that calculates the Root of a MerkleTree
// given the list of siblings, direction and the leaf
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

// Semaphore is the structure representing the Semaphore v3.0 circuit.
// NullifierHash and MTRoot are inputs to assert equality with
// the respective values calculated by the circuit.
// Levels is the size of the MerkleTree.
// At the moment field tags are unused by reilabs/gnark-lean-extractor,
// but they are present here for readability
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

// AbsDefine circuit specification reference is available here
// https://github.com/semaphore-protocol/semaphore/blob/main/packages/circuits/semaphore.circom
func (circuit *Semaphore) AbsDefine(api abstractor.API) error {
	secret := api.Call(Poseidon2{circuit.IdentityNullifier, circuit.IdentityTrapdoor})[0]
	identityCommitment := api.Call(Poseidon1{secret})[0]
	nullifierHash := api.Call(Poseidon2{circuit.ExternalNullifier, circuit.IdentityNullifier})[0]
	api.AssertIsEqual(nullifierHash, circuit.NullifierHash) // Assert circuit is correct

	root := api.Call(MerkleTreeInclusionProof{
		Leaf:        identityCommitment,
		PathIndices: circuit.TreePathIndices,
		Siblings:    circuit.TreeSiblings,
	})[0]

	api.AssertIsEqual(root, circuit.MTRoot) // Assert circuit is correct

	// As per circuit implementation, we calculate the square of the signal hash
	// even if the result is unused
	api.Mul(circuit.SignalHash, circuit.SignalHash)

	return nil
}

func (circuit Semaphore) Define(api frontend.API) error {
	return abstractor.Concretize(api, &circuit)
}

func testSemaphore() (string, error) {
	nLevels := 20
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
	var outFile string

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
						Destination: &outFile,
					},
				},
				Action: func(cCtx *cli.Context) error {
					circuitString, err := testSemaphore()
					if err != nil {
						log.Fatal(err)
					}
					absPath, _ := filepath.Abs(outFile)
					err = os.MkdirAll(filepath.Dir(absPath), 0666)
					if err != nil && !os.IsExist(err) {
						log.Fatal(err)
					}
					err = os.WriteFile(absPath, []byte(circuitString), 0666)
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
