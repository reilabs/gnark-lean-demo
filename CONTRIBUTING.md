# Contributing

This document exists as a brief introduction for how you can contribute to this
demo repository. It includes a guide to
[the structure of the repository](#repository-structure),
[building and testing](#building-and-testing) and
[getting your code on `main`](#getting-your-code-on-main).

If you are new to Go or Lean, there are also corresponding guides to
getting started [with Go](#new-to-go) and [with Lean](#new-to-lean), in which we
provide some good resources for getting started.

## Repository Structure

The Go circuit that is being verified in this demo is defined in
[`semaphore.go`](go-circuit/semaphore.go) and contains an implementation of the
Semaphore protocol using the aforementioned gnark library for the Go language.
This is a reimplementation of the original
[circom circuit](https://github.com/semaphore-protocol/semaphore/blob/main/packages/circuits/semaphore.circom)
developed for the Semaphore protocol.

This implementation makes use of the
[`AbsDefine`](https://github.com/reilabs/gnark-lean-extractor/blob/main/abstractor/abstractor.go#L23)
function from the Gnark Extractor to mark calls to gadgets, hence helping to
create readable code in the extracted Lean.

The result of the automatic translation from the Go circuit to Lean can be seen
in [`LeanCircuit.lean`](lean-circuit/LeanCircuit.lean).

For more information on how to re-run the extraction, or verify the generated
Lean, see [below](#building-and-testing).

## Building and Testing

We recommend that you do not take our word for it that this works and that the
proofs verify, but that you should try it yourself!

The first step in doing this is to build the go project and run the extraction
to Lean yourself. This can be done as follows.

1. Clone the repository into a location of your choice.

```sh
git clone https://github.com/reilabs/gnark-lean-demo gnark-lean-demo
```

2. Build the go circuit project using `go` (meaning that you will need to have
   that toolchain set up).

```sh
cd gnark-lean-demo/go-circuit
go build
```

3. Extract the circuit into place in the Lean project.

```sh
./go-circuit extract-circuit --out ../lean-circuit/LeanCircuit.lean
```

Running this extraction on the Go implementation of the circuit produces an
equivalent implementation of this circuit in Lean. You can verify that
implementation and the accompanying proofs as follows:

1. Change directory to the lean project.

```sh
cd ../lean-circuit
```

2. Build the lean project, thereby verifying it. This relies on having the
   `lake` build tool for Lean on your path.

```sh
lake build
```

## Getting Your Code on `main`

This repository works on a fork and
[pull request](https://github.com/reilabs/gnark-lean-demo/pulls) workflow, with
code review and CI as an integral part of the process. This works as follows:

1. If necessary, you fork the repository, but if you have access to do so please
   create a branch.
2. You make your changes on that branch.
3. Pull request that branch against main.
4. The pull request will be reviewed and CI will be run on it.
5. Once the reviewer(s) have accepted the code and CI has passed, the code will
   be merged to `main`.

## New to Go?

If you are new to working with [Go](https://go.dev), a great place to start is
the official set of [tutorials](https://go.dev/learn/). They explain how to
[install](https://go.dev/doc/install) and set the language up, as well as an
[interactive tour](https://go.dev/tour/welcome/1) of how to use the language.

We recommend being familiar with the language and the `go` command-line
interface to the build system and compiler before interacting with the Go
portion of this repository.

## New to Lean?

If you are new to working with [Lean](https://leanprover.github.io), the best
starting point is the [Lean 4 Manual](https://leanprover.github.io/lean4/doc/).

While that guide contains sections on using Lean for both theorem proving and as
a programming language, we recommend following the
[theorem proving in Lean 4](https://leanprover.github.io/theorem_proving_in_lean4/)
tutorial. We also recommend looking at
[mathematics in lean](https://leanprover-community.github.io/mathematics_in_lean/index.html),
and the documentation for [mathlib 4](https://leanprover-community.github.io/mathlib4_docs/)
as the concepts there are used in the dependencies of this demo.

Note that many of the resources on lean are for the old Lean 3 version. This
project, and Reilabs in general, make use of the new Lean 4 implementation for
its many
[enhancements](https://leanprover.github.io/lean4/doc/lean3changes.html). There
is no compatibility between the two versions, so please check that any resources
you find are for the correct version.

