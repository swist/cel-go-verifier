package verifier

import "github.com/swist/cel-go-verifier/smt"

// MkOrFlattened builds a disjunction, pruning literal true and false operands.
// It returns false for no operands and the operand itself for one.
func MkOrFlattened(c *smt.Context, args ...*smt.Term) *smt.Term {
	var filtered []*smt.Term
	for _, a := range args {
		if a.IsTrue() {
			return c.MkTrue()
		}
		if !a.IsFalse() {
			filtered = append(filtered, a)
		}
	}
	switch len(filtered) {
	case 0:
		return c.MkFalse()
	case 1:
		return filtered[0]
	}
	return c.MkOr(filtered...)
}

// MkAndFlattened builds a conjunction, pruning literal true and false operands.
// It returns true for no operands and the operand itself for one.
func MkAndFlattened(c *smt.Context, args ...*smt.Term) *smt.Term {
	var filtered []*smt.Term
	for _, a := range args {
		if a.IsFalse() {
			return c.MkFalse()
		}
		if !a.IsTrue() {
			filtered = append(filtered, a)
		}
	}
	switch len(filtered) {
	case 0:
		return c.MkTrue()
	case 1:
		return filtered[0]
	}
	return c.MkAnd(filtered...)
}

// MkNotFlattened negates arg, folding literals.
func MkNotFlattened(c *smt.Context, arg *smt.Term) *smt.Term {
	switch {
	case arg.IsTrue():
		return c.MkFalse()
	case arg.IsFalse():
		return c.MkTrue()
	}
	return c.MkNot(arg)
}

// SwitchBuilder builds a chain of nested if-then-else terms. Cases are tried
// in the order they are added; cases whose condition is literally false are
// dropped, and ite(c, x, x) is never built.
type SwitchBuilder struct {
	c     *smt.Context
	conds []*smt.Term
	vals  []*smt.Term
}

// NewSwitch returns an empty switch.
func NewSwitch(c *smt.Context) *SwitchBuilder { return &SwitchBuilder{c: c} }

// Case adds a case.
func (s *SwitchBuilder) Case(cond, val *smt.Term) *SwitchBuilder {
	if cond.IsFalse() {
		return s
	}
	s.conds = append(s.conds, cond)
	s.vals = append(s.vals, val)
	return s
}

// Build returns the chain, falling back to def.
func (s *SwitchBuilder) Build(def *smt.Term) *smt.Term {
	result := def
	for i := len(s.conds) - 1; i >= 0; i-- {
		if s.vals[i] == result {
			continue
		}
		result = s.c.MkITE(s.conds[i], s.vals[i], result)
	}
	return result
}
