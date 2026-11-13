package kube

import (
	"fmt"
	"math"
	"math/big"

	"cel.dev/cel-go/common/types"
	"cel.dev/cel-go/common/types/ref"
	"gopkg.in/inf.v0"
	"k8s.io/apimachinery/pkg/api/resource"
	apiservercel "k8s.io/apiserver/pkg/cel"

	"github.com/swist/cel-go-verifier/smt"
	"github.com/swist/cel-go-verifier/verifier"
)

// Quantities are encoded by their value in nano units: resource.Quantity
// rounds to nano precision on parsing, and its arithmetic is exact. Equality,
// comparisons and arithmetic depend only on the value, but isInteger and
// asInteger also depend on how the quantity is written (1000m is no integer),
// so they're exact only for constants.

var nanosPerUnit = big.NewInt(1_000_000_000)

// quantityNanos returns the value of q in nano units, if it's a whole number of them.
func quantityNanos(q *resource.Quantity) (*big.Int, bool) {
	d := q.AsDec()
	scale := int64(d.Scale())
	if scale > 9 {
		return nil, false
	}
	n := new(big.Int).Set(d.UnscaledBig())
	return n.Mul(n, new(big.Int).Exp(big.NewInt(10), big.NewInt(9-scale), nil)), true
}

func quantityFromNanos(n *big.Int) *resource.Quantity {
	q := resource.NewDecimalQuantity(*inf.NewDecBig(n, 9), resource.DecimalSI)
	return q
}

func defineQuantity(c *smt.Context, ts *verifier.TypeSystem, sink func(*smt.Term), r, nanos *smt.Term) *smt.Term {
	return ts.DefineObject(sink, r, quantityType, verifier.ObjectField{Name: "nanos", Value: ts.WrapInt(nanos)})
}

func nanos(ts *verifier.TypeSystem, q *smt.Term) *smt.Term { return intField(ts, q, "nanos") }

var quantityConversion = conversion{
	literal: func(c *smt.Context, ts *verifier.TypeSystem, sink func(*smt.Term), s string) (*smt.Term, bool) {
		v, ok := eval("quantity(a)", types.String(s)).(apiservercel.Quantity)
		if !ok {
			return nil, false
		}
		return constQuantity(c, ts, sink, v.Quantity)
	},
	symbolic: func(c *smt.Context, ts *verifier.TypeSystem, sink func(*smt.Term), s *smt.Term) (*smt.Term, *smt.Term) {
		str := c.StringSort()
		r := c.MkApp(fn(ts, "quantity_of", ts.MessageRefSort(), str), s)
		n := c.MkApp(fn(ts, "quantity_nanos", c.IntSort(), str), s)
		valid := c.MkApp(fn(ts, "is_quantity", c.BoolSort(), str), s)
		return defineQuantity(c, ts, sink, r, n), valid
	},
}

func constQuantity(c *smt.Context, ts *verifier.TypeSystem, sink func(*smt.Term), q *resource.Quantity) (*smt.Term, bool) {
	n, ok := quantityNanos(q)
	if !ok {
		return nil, false
	}
	// The key keeps the representation, which isInteger depends on.
	r := constObject(c, ts, "quantity:"+q.String()+"#"+fmt.Sprint(q.AsDec().Scale()), q)
	return defineQuantity(c, ts, sink, r, c.MkIntBig(n)), true
}

func quantityAxioms() []*verifier.FunctionAxiom {
	conv := newAxiom("quantity")
	unaryOverload(conv, "string_to_quantity", quantityConversion.translate)
	isQ := newAxiom("isQuantity")
	unaryOverload(isQ, "is_quantity_string", quantityConversion.validity)

	sign := newAxiom("sign").Unary("quantity_sign", func(c *smt.Context, ts *verifier.TypeSystem, _ func(*smt.Term), q *smt.Term) (*smt.Term, bool) {
		return cmpInts(c, ts, nanos(ts, q), c.MkInt(0)), true
	}, false)
	cmp := func(f func(c *smt.Context, ts *verifier.TypeSystem, a, b *smt.Term) *smt.Term) verifier.BinaryTranslator {
		return func(c *smt.Context, ts *verifier.TypeSystem, _ func(*smt.Term), a, b *smt.Term) (*smt.Term, bool) {
			return f(c, ts, nanos(ts, a), nanos(ts, b)), true
		}
	}
	gt := newAxiom("isGreaterThan").Binary("quantity_is_greater_than", cmp(func(c *smt.Context, ts *verifier.TypeSystem, a, b *smt.Term) *smt.Term {
		return ts.WrapBool(c.MkGt(a, b))
	}))
	lt := newAxiom("isLessThan").Binary("quantity_is_less_than", cmp(func(c *smt.Context, ts *verifier.TypeSystem, a, b *smt.Term) *smt.Term {
		return ts.WrapBool(c.MkLt(a, b))
	}))
	compareTo := newAxiom("compareTo").Binary("quantity_compare_to", cmp(cmpInts))

	arith := func(sub, withInt bool) verifier.BinaryTranslator {
		return func(c *smt.Context, ts *verifier.TypeSystem, sink func(*smt.Term), a, b *smt.Term) (*smt.Term, bool) {
			x := nanos(ts, a)
			var y *smt.Term
			if withInt {
				y = c.MkMul(ts.GetInt(b), c.MkIntBig(nanosPerUnit))
			} else {
				y = nanos(ts, b)
			}
			var n *smt.Term
			if sub {
				n = c.MkSub(x, y)
			} else {
				n = c.MkAdd(x, y)
			}
			name := "quantity_add"
			if sub {
				name = "quantity_sub"
			}
			r := c.MkApp(fn(ts, name, ts.MessageRefSort(), ts.CelValueSort(), ts.CelValueSort()), a, b)
			return defineQuantity(c, ts, sink, r, n), true
		}
	}
	add := newAxiom("add").Binary("quantity_add", arith(false, false)).Binary("quantity_add_int", arith(false, true))
	sub := newAxiom("sub").Binary("quantity_sub", arith(true, false)).Binary("quantity_sub_int", arith(true, true))

	isInteger := newAxiom("isInteger")
	unaryOverload(isInteger, "quantity_is_integer", func(c *smt.Context, ts *verifier.TypeSystem, sink func(*smt.Term), q *smt.Term) (*smt.Term, *smt.Term) {
		if k, ok := constantOf(ts, q); ok {
			_, ok := k.(*resource.Quantity).AsInt64()
			return ts.MkBool(ok), c.MkFalse()
		}
		possible, repr := integerRepresentation(c, ts, q)
		return ts.WrapBool(c.MkAnd(possible, repr)), possible
	})
	asInteger := newAxiom("asInteger")
	unaryOverload(asInteger, "quantity_get_int", func(c *smt.Context, ts *verifier.TypeSystem, sink func(*smt.Term), q *smt.Term) (*smt.Term, *smt.Term) {
		if k, ok := constantOf(ts, q); ok {
			if i, ok := k.(*resource.Quantity).AsInt64(); ok {
				return ts.MkInt(i), c.MkFalse()
			}
			return ts.MkError(), c.MkFalse()
		}
		possible, repr := integerRepresentation(c, ts, q)
		value := ts.WrapInt(c.MkDiv(nanos(ts, q), c.MkIntBig(nanosPerUnit)))
		return c.MkITE(c.MkAnd(possible, repr), value, ts.MkError()), possible
	})
	asFloat := newAxiom("asApproximateFloat")
	unaryOverload(asFloat, "quantity_get_float", func(c *smt.Context, ts *verifier.TypeSystem, sink func(*smt.Term), q *smt.Term) (*smt.Term, *smt.Term) {
		if k, ok := constantOf(ts, q); ok {
			return ts.MkDouble(k.(*resource.Quantity).AsApproximateFloat64()), c.MkFalse()
		}
		// The approximation depends on the representation too, so it's a fresh choice per expression.
		d := c.MkConst(fmt.Sprintf("!kube.quantity_float#%d", q.ID()), c.FPSortDouble())
		sink(c.MkNot(c.MkFPIsNaN(d)))
		return ts.WrapDouble(d), c.MkTrue()
	})
	return []*verifier.FunctionAxiom{conv, isQ, sign, gt, lt, compareTo, add, sub, isInteger, asInteger, asFloat}
}

// integerRepresentation returns when q's value is an int64, which isInteger
// requires, and whether q is written as an integer, which is unknown for a
// non-constant (it's a fresh choice per expression).
func integerRepresentation(c *smt.Context, ts *verifier.TypeSystem, q *smt.Term) (possible, repr *smt.Term) {
	n := nanos(ts, q)
	unit := c.MkIntBig(nanosPerUnit)
	whole := c.MkDiv(n, unit)
	possible = c.MkAnd(
		c.MkEq(c.MkMod(n, unit), c.MkInt(0)),
		c.MkGe(whole, c.MkInt(math.MinInt64)),
		c.MkLe(whole, c.MkInt(math.MaxInt64)))
	repr = c.MkConst(fmt.Sprintf("!kube.quantity_written_as_integer#%d", q.ID()), c.BoolSort())
	return possible, repr
}

func formatQuantity(fields map[string]verifier.MessageField) (ref.Val, string, bool) {
	n, ok := verifier.BigIntField(fields["nanos"])
	if !ok {
		return nil, "", false
	}
	q := quantityFromNanos(n)
	return apiservercel.Quantity{Quantity: q}, fmt.Sprintf("quantity('%s')", q.String()), true
}
