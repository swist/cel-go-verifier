// Package z3cgo is an smt.Backend that links libz3 through cgo. It is only
// built with the z3cgo build tag, so that users of the verifier don't need
// libz3 unless they ask for it:
//
//	CGO_CFLAGS=-I/path/to/z3/include CGO_LDFLAGS=-L/path/to/z3/lib go build -tags z3cgo
//
// Without the tag, New panics and Enabled is false.
package z3cgo
