#!/usr/bin/env bash

go mod download
go build -o gnark-lean-demo -v ./...
bash gnark-lean-demo extract-circuit --out=lean-circuit/LeanCircuit.lean