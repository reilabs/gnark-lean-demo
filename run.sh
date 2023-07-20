#!/usr/bin/env bash

go mod download
go build -v ./...
go-circuit extract-circuit --out=lean-circuit/LeanCircuit.lean