<a href="https://reilabs.io">
<picture>
  <source width="150" media="(prefers-color-scheme: dark)" srcset="https://github.com/reilabs/gnark-lean-extractor/assets/35899/c04bdb7f-4c31-4264-acb6-a96f32c6cc29">
  <source width="150" media="(prefers-color-scheme: light)" srcset="https://github.com/reilabs/gnark-lean-extractor/assets/35899/fc11280b-e3e5-4a6f-83da-788884083c36">
  <img width="150" src="https://github.com/reilabs/gnark-lean-extractor/assets/35899/fc11280b-e3e5-4a6f-83da-788884083c36">
</picture>
</a>

# Formal Verification of Gnark Circuits

This repository contains an example of using Reilabs'
[gnark-lean-extractor](https://github.com/reilabs/gnark-lean-extractor) library
to prove the correctness of a [gnark](https://github.com/ConsenSys/gnark)
reimplementation of the circuits necessary to implement and operate the
[Semaphore](https://semaphore.appliedzkp.org) protocol.

Under the hood, this repository makes heavy use of Reilabs'
[proven-zk](https://github.com/reilabs/proven-zk) library. It is a
[lean](https://leanprover.github.io) library to aid in the formal verification
of circuits produced by the extractor.

For guidelines on how to build these things for yourself, or to contribute to
the repository, see our [contributing guide](./CONTRIBUTING.md). It also
contains a guide to the structure of the repository.

## Verified Properties

The [main lean file](lean-circuit/Main.lean) contains formulations and
accompanying proofs of the following properties for the circuit.

1. **Poseidon Equivalence:** The equivalence of the
   [Poseidon hash implementation](./go-circuit/poseidon.go) to an
   [implementation](./lean-circuit/LeanCircuit/Poseidon/Spec.lean) very closely
   based on the Poseidon
   [reference implementation](https://extgit.iaik.tugraz.at/krypto/hadeshash).
2. **No Censorship:** A proof, given knowledge of secrets relating to
   an identity and that the identity commitment being included in the tree, that
   it is _always_ possible to generate a valid proof.
3. **No Double Signalling:** A proof that any attempt to signal twice using the
   same identity commitment will result in the equality of the corresponding
   nullifier hashes.
4. **No Unauthorized Signalling:** A proof that it is not possible to have the
   circuit accept a proof where the identity commitment generating that proof is
   not already included in the tree of identity commitments.

