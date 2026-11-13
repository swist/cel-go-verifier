package verifier

import (
	"fmt"
	"strings"

	"cel.dev/cel-go/common/types"

	"github.com/swist/cel-go-verifier/smt"
)

// translationContext is the state shared by the translators of one query.
type translationContext struct {
	c                *smt.Context
	ts               *TypeSystem
	tcg              *typeConstraintGenerator
	unrollLimit      int
	constraints      []*smt.Term
	constraintSet    map[*smt.Term]bool
	inputVars        []*smt.Term
	inputVarTypes    map[*smt.Term]*types.Type
	unmodeledResults []*smt.Term
	approxDescs      []string
	approxTerms      map[string][]*smt.Term
	symbolTable      map[string]tv
	localScope       map[string]tv
}

func newTranslationContext(c *smt.Context, ts *TypeSystem, unrollLimit int) *translationContext {
	return &translationContext{
		c: c, ts: ts, tcg: &typeConstraintGenerator{c: c, ts: ts, unrollLimit: unrollLimit},
		unrollLimit: unrollLimit, constraintSet: map[*smt.Term]bool{},
		inputVarTypes: map[*smt.Term]*types.Type{}, approxTerms: map[string][]*smt.Term{},
		symbolTable: map[string]tv{}, localScope: map[string]tv{},
	}
}

func (x *translationContext) addConstraint(t *smt.Term) {
	if !x.constraintSet[t] {
		x.constraintSet[t] = true
		x.constraints = append(x.constraints, t)
	}
}

// constrainValidValue constrains value to be a CEL value whenever guard holds.
func (x *translationContext) constrainValidValue(guard, value *smt.Term) {
	x.addConstraint(x.c.MkImplies(guard, x.ts.IsValidValue(value)))
}

func (x *translationContext) addInputVariable(v *smt.Term, t *types.Type) {
	if _, ok := x.inputVarTypes[v]; !ok {
		x.inputVars = append(x.inputVars, v)
	}
	x.inputVarTypes[v] = t
}

// guaranteedType is the declared type of an input variable, or dyn.
func (x *translationContext) guaranteedType(v *smt.Term) *types.Type {
	if t, ok := x.inputVarTypes[v]; ok {
		return t
	}
	return types.DynType
}

// isTruncatedMap holds for maps with more keys than the unroll limit.
func (x *translationContext) isTruncatedMap(v *smt.Term) *smt.Term {
	c, ts := x.c, x.ts
	return x.recordUnrollLimitApproximation(c.MkAnd(
		ts.IsMap(v),
		c.MkGt(c.MkLength(ts.GetMapKeys(ts.GetMapRef(v))), c.MkInt(int64(x.unrollLimit)))))
}

// recordApproximation records description as a reason results are
// approximate where cond holds, and returns the term to use for cond.
func (x *translationContext) recordApproximation(description string, cond *smt.Term) *smt.Term {
	term := cond
	if cond.IsTrue() {
		term = x.c.MkFreshConst("!approx", x.c.BoolSort())
		x.addConstraint(term)
	}
	if _, ok := x.approxTerms[description]; !ok {
		x.approxDescs = append(x.approxDescs, description)
	}
	x.approxTerms[description] = append(x.approxTerms[description], term)
	return term
}

func (x *translationContext) recordUnrollLimitApproximation(cond *smt.Term) *smt.Term {
	return x.recordApproximation(fmt.Sprintf("lists and maps longer than the unroll limit (%d)", x.unrollLimit), cond)
}

func (x *translationContext) recordCallApproximation(fn string, cond *smt.Term) *smt.Term {
	return x.recordApproximation("calls to `"+fn+"`", cond)
}

// approximationSources returns the descriptions of the approximations that
// alone make taint hold in m.
func (x *translationContext) approximationSources(m smt.Model, taint *smt.Term) ([]string, error) {
	var out []string
	for _, d := range x.approxDescs {
		var others []*smt.Term
		for _, o := range x.approxDescs {
			if o != d {
				others = append(others, x.approxTerms[o]...)
			}
		}
		v, err := m.Eval(x.withoutApproximation(taint, others), true)
		if err != nil {
			return nil, err
		}
		if v.IsTrue() {
			out = append(out, d)
		}
	}
	return out, nil
}

func (x *translationContext) withoutApproximation(e *smt.Term, terms []*smt.Term) *smt.Term {
	falses := make([]*smt.Term, len(terms))
	for i := range falses {
		falses[i] = x.c.MkFalse()
	}
	return x.c.Substitute(e, terms, falses)
}

func (x *translationContext) addUnmodeledResult(cond *smt.Term) {
	x.unmodeledResults = append(x.unmodeledResults, cond)
}

func (x *translationContext) hasUnmodeledResult() *smt.Term {
	return MkOrFlattened(x.c, x.unmodeledResults...)
}

func (x *translationContext) bindSymbol(name string, v tv) { x.localScope[name] = v }

func (x *translationContext) lookupSymbol(name string) (tv, bool) {
	v, ok := x.localScope[name]
	return v, ok
}

func (x *translationContext) computeSymbolIfAbsent(raw string, f func(string) tv) tv {
	if !strings.HasPrefix(raw, ".") {
		if v, ok := x.localScope[raw]; ok {
			return v
		}
	}
	name := strings.TrimPrefix(raw, ".")
	if v, ok := x.symbolTable[name]; ok {
		return v
	}
	v := f(name)
	x.symbolTable[name] = v
	return v
}

// withScope binds name to v while running f, then restores the previous binding.
func withScope[T any](x *translationContext, name string, v tv, f func() T) T {
	prev, had := x.localScope[name]
	x.localScope[name] = v
	defer func() {
		if had {
			x.localScope[name] = prev
		} else {
			delete(x.localScope, name)
		}
	}()
	return f()
}
