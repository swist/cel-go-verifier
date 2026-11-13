package verifier

import (
	"fmt"

	"cel.dev/cel-go/common/decls"
	"cel.dev/cel-go/common/types"

	"github.com/swist/cel-go-verifier/smt"
)

// FunctionDecl declares a CEL function for the purpose of axiomatization. The
// order of the overloads determines the order in which dynamically dispatched
// calls test them.
type FunctionDecl struct {
	Name      string
	Overloads []OverloadDecl
}

// OverloadDecl is one overload of a FunctionDecl.
type OverloadDecl struct {
	ID     string
	Params []*types.Type
	Result *types.Type
}

// FunctionDeclFromCEL converts a cel-go function declaration, keeping its overload order.
func FunctionDeclFromCEL(fn *decls.FunctionDecl) FunctionDecl {
	out := FunctionDecl{Name: fn.Name()}
	for _, o := range fn.OverloadDecls() {
		out.Overloads = append(out.Overloads, OverloadDecl{ID: o.ID(), Params: o.ArgTypes(), Result: o.ResultType()})
	}
	return out
}

// OverloadResult is the translation of an overload: its value and the
// condition under which the value may differ from the runtime's.
type OverloadResult struct {
	Value  *smt.Term
	Approx *smt.Term
}

// OverloadTranslator translates one overload. args are the CelValue terms of
// the arguments, and argApprox their approximation conditions. Global
// constraints go to sink; they must be guarded by the argument types, since
// the overload's result is only used where its type guard holds. It returns
// false if it doesn't handle the call.
type OverloadTranslator func(c *smt.Context, ts *TypeSystem, sink func(*smt.Term), args, argApprox []*smt.Term) (OverloadResult, bool)

// UnaryTranslator translates an overload of one argument; the result's approximation is the argument's.
type UnaryTranslator func(c *smt.Context, ts *TypeSystem, sink func(*smt.Term), arg *smt.Term) (*smt.Term, bool)

// BinaryTranslator translates an overload of two arguments.
type BinaryTranslator func(c *smt.Context, ts *TypeSystem, sink func(*smt.Term), a, b *smt.Term) (*smt.Term, bool)

// TernaryTranslator translates an overload of three arguments.
type TernaryTranslator func(c *smt.Context, ts *TypeSystem, sink func(*smt.Term), a, b, d *smt.Term) (*smt.Term, bool)

// FunctionAxiom is the axiomatization of a CEL function: its declaration and
// translators for (some of) its overloads. Calls whose candidate overloads
// lack a translator are uninterpreted.
type FunctionAxiom struct {
	Decl        FunctionDecl
	Translators map[string]OverloadTranslator
}

// NewFunctionAxiom starts an axiom for decl.
func NewFunctionAxiom(decl FunctionDecl) *FunctionAxiom {
	return &FunctionAxiom{Decl: decl, Translators: map[string]OverloadTranslator{}}
}

// Overload adds a translator for an overload.
func (f *FunctionAxiom) Overload(id string, t OverloadTranslator) *FunctionAxiom {
	if _, dup := f.Translators[id]; dup {
		panic(fmt.Sprintf("verifier: duplicate translator for %s", id))
	}
	f.Translators[id] = t
	return f
}

// Unary adds a translator for a one-argument overload. If approximated, results
// other than unknowns are always approximate.
func (f *FunctionAxiom) Unary(id string, t UnaryTranslator, approximated bool) *FunctionAxiom {
	return f.Overload(id, func(c *smt.Context, ts *TypeSystem, sink func(*smt.Term), args, approx []*smt.Term) (OverloadResult, bool) {
		if len(args) != 1 {
			panic(fmt.Sprintf("%s overload requires exactly 1 argument", id))
		}
		v, ok := t(c, ts, sink, args[0])
		if !ok {
			return OverloadResult{}, false
		}
		a := approx[0]
		if approximated {
			a = c.MkITE(ts.IsUnknown(v), a, c.MkTrue())
		}
		return OverloadResult{v, a}, true
	})
}

// Binary adds a translator for a two-argument overload.
func (f *FunctionAxiom) Binary(id string, t BinaryTranslator) *FunctionAxiom {
	return f.Overload(id, func(c *smt.Context, ts *TypeSystem, sink func(*smt.Term), args, approx []*smt.Term) (OverloadResult, bool) {
		if len(args) != 2 {
			panic(fmt.Sprintf("%s overload requires exactly 2 arguments", id))
		}
		v, ok := t(c, ts, sink, args[0], args[1])
		if !ok {
			return OverloadResult{}, false
		}
		return OverloadResult{v, c.MkOr(approx[0], approx[1])}, true
	})
}

// Ternary adds a translator for a three-argument overload.
func (f *FunctionAxiom) Ternary(id string, t TernaryTranslator) *FunctionAxiom {
	return f.Overload(id, func(c *smt.Context, ts *TypeSystem, sink func(*smt.Term), args, approx []*smt.Term) (OverloadResult, bool) {
		if len(args) != 3 {
			panic(fmt.Sprintf("%s overload requires exactly 3 arguments", id))
		}
		v, ok := t(c, ts, sink, args[0], args[1], args[2])
		if !ok {
			return OverloadResult{}, false
		}
		return OverloadResult{v, c.MkOr(approx[0], c.MkOr(approx[1], approx[2]))}, true
	})
}

// functionRegistry indexes axioms by function and overload.
type functionRegistry struct {
	decls       map[string]FunctionDecl
	translators map[string]OverloadTranslator
}

func newFunctionRegistry(axioms []*FunctionAxiom) (*functionRegistry, error) {
	r := &functionRegistry{decls: map[string]FunctionDecl{}, translators: map[string]OverloadTranslator{}}
	for _, a := range axioms {
		if _, dup := r.decls[a.Decl.Name]; dup {
			return nil, fmt.Errorf("verifier: duplicate axiom for function %s", a.Decl.Name)
		}
		r.decls[a.Decl.Name] = a.Decl
		for id, t := range a.Translators {
			if _, dup := r.translators[id]; dup {
				return nil, fmt.Errorf("verifier: duplicate translator for overload %s", id)
			}
			r.translators[id] = t
		}
	}
	return r, nil
}
