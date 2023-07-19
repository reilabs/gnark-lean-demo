#!/usr/bin/env pwsh

Write-Host "It's recommended to avoid PowerShell to prevent any symbol encoding error"

# Powershell uses different encoding which means it's struggling to append
# math symbols to file
go mod download
go run go-circuit/semaphore.go > lean-circuit/LeanCircuit.lean