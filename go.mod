module github.com/reilabs/gnark-lean-demo

go 1.20

require (
	github.com/consensys/gnark v0.8.0
	github.com/consensys/gnark-crypto v0.9.1
	github.com/reilabs/gnark-lean-extractor v0.0.0
	github.com/urfave/cli/v2 v2.25.7
)

replace github.com/reilabs/gnark-lean-extractor => ../gnark-lean-extractor

require (
	github.com/blang/semver/v4 v4.0.0 // indirect
	github.com/consensys/bavard v0.1.13 // indirect
	github.com/cpuguy83/go-md2man/v2 v2.0.2 // indirect
	github.com/mattn/go-colorable v0.1.12 // indirect
	github.com/mattn/go-isatty v0.0.14 // indirect
	github.com/mmcloughlin/addchain v0.4.0 // indirect
	github.com/rs/zerolog v1.29.0 // indirect
	github.com/russross/blackfriday/v2 v2.1.0 // indirect
	github.com/xrash/smetrics v0.0.0-20201216005158-039620a65673 // indirect
	golang.org/x/sys v0.5.0 // indirect
	rsc.io/tmplfunc v0.0.3 // indirect
)
