# Formal verification of gnark circuits

This repo showcases the use of [gnark-lean-extractor](https://github.com/reilabs/gnark-lean-extractor)
to prove correctness of a gnark reimplementation of the Semaphore
protocol circuits.

## Repo structure

The circuit is defined in [semaphore.go](go-circuit/semaphore.go) and is a reimplementation
of the original circom circuit. It uses the Lean extractor's `AbsDefine` API,
to mark gadget calls, resulting in very readable code on the Lean side.
The result of automatic translation can be viewed in [LeanCircuit.lean](lean-circuit/LeanCircuit.lean).
It can also be regenerated, by running `./go-circuit extract-circuit --out=lean-circuit/LeanCircuit.lean`.

## Verified properties

The [main Lean file](lean-circuit/Main.lean) contains formulations and proofs of the following properties:
1. The equivalence of the Poseidon hash implementation to an implementation very closely based
   on the Poseidon reference implementation. That implementation can be reviewed in [this file](lean-circuit/LeanCircuit/Poseidon/Spec.lean).
2. No censorship: given the knowledge of secrets relating to an identity and the identity commitment being included in tree,
   it is always possible to generate a valid proof.
3. No double signalling: any attempt to signal twice using the same identity commitment will result in the equality of
   nullifier hashes.
4. No unauthorized signalling: it is not possible to have the circuit accept a proof where the identity commitment
   is not included in the tree.