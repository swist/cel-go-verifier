//go:build z3cgo

package main

import (
	"github.com/swist/cel-go-verifier/smt"
	"github.com/swist/cel-go-verifier/smt/z3cgo"
)

func cgoBackend() (smt.Backend, error) { return z3cgo.New(), nil }
