#!/usr/bin/env pwsh

go mod download
go build -o gnark-lean-demo.exe -v ./...
.\gnark-lean-demo.exe extract-circuit --out=lean-circuit/LeanCircuit.lean