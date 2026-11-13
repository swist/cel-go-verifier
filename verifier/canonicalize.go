package verifier

import (
	"errors"

	"cel.dev/cel-go/cel"
)

// canonicalizePair canonicalizes both ASTs before an equivalence check.
func (v *Verifier) canonicalizePair(a, b *cel.Ast) (*cel.Ast, *cel.Ast, error) {
	return nil, nil, errors.New("not implemented")
}
