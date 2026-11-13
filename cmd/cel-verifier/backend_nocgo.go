//go:build !z3cgo

package main

import (
	"errors"

	"github.com/swist/cel-go-verifier/smt"
)

func cgoBackend() (smt.Backend, error) {
	return nil, errors.New("the cgo backend needs a build with -tags z3cgo")
}
