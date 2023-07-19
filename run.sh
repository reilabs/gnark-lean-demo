#!/usr/bin/env bash

go mod download
go run go-circuit/semaphore.go > lean-circuit/LeanCircuit.lean