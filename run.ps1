#!/usr/bin/env pwsh

go mod download
go build -v ./...
.\go-circuit.exe extract-circuit --out=lean-circuit/LeanCircuit.lean