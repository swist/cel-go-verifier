//go:build !z3cgo

package z3cgo

import (
	"time"

	"github.com/swist/cel-go-verifier/smt"
)

// Enabled reports whether the package was built with the z3cgo tag.
const Enabled = false

// Backend is unavailable without the z3cgo build tag.
type Backend struct{}

// New panics: build with -tags z3cgo.
func New() *Backend { panic("z3cgo: built without the z3cgo tag") }

// Simplify implements smt.Backend.
func (*Backend) Simplify(*smt.Context, *smt.Term) *smt.Term { panic("z3cgo: unavailable") }

// NewSolver implements smt.Backend.
func (*Backend) NewSolver(*smt.Context, time.Duration) (smt.Solver, error) {
	panic("z3cgo: unavailable")
}

// Close implements smt.Backend.
func (*Backend) Close(*smt.Context) {}
