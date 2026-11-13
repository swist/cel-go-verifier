//go:build z3cgo

package verifier_test

import (
	"github.com/swist/cel-go-verifier/smt"
	"github.com/swist/cel-go-verifier/smt/z3cgo"
)

func init() {
	testBackend = func() smt.Backend { return z3cgo.New() }
	cgoBackend = true
}
