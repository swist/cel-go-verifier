package kube

import (
	"github.com/swist/cel-go-verifier/smt"
	"github.com/swist/cel-go-verifier/verifier"
)

// The lists extensions are unrolled over the first UnrollLimit elements,
// like comprehensions: results on longer lists are approximate, as are
// results that depend on elements whose comparison or equality isn't modeled
// exactly (NaN, mixed numeric kinds in dyn lists, aggregates).

// elemKind describes how the lists extensions treat an element type.
type elemKind struct {
	name string
	is   func(ts *verifier.TypeSystem, v *smt.Term) *smt.Term
	// less is the strict order of unwrapped values.
	less func(c *smt.Context, ts *verifier.TypeSystem, a, b *smt.Term) *smt.Term
	// inexact tests values whose order isn't modeled (NaN).
	inexact func(c *smt.Context, ts *verifier.TypeSystem, v *smt.Term) *smt.Term
}

func intLess(get func(*verifier.TypeSystem, *smt.Term) *smt.Term) func(c *smt.Context, ts *verifier.TypeSystem, a, b *smt.Term) *smt.Term {
	return func(c *smt.Context, ts *verifier.TypeSystem, a, b *smt.Term) *smt.Term {
		return c.MkLt(get(ts, a), get(ts, b))
	}
}

var elemKinds = []elemKind{
	{name: "int", is: (*verifier.TypeSystem).IsInt, less: intLess((*verifier.TypeSystem).GetInt)},
	{name: "uint", is: (*verifier.TypeSystem).IsUint, less: intLess((*verifier.TypeSystem).GetUint)},
	{name: "double", is: (*verifier.TypeSystem).IsDouble,
		less: func(c *smt.Context, ts *verifier.TypeSystem, a, b *smt.Term) *smt.Term {
			return c.MkFPLt(ts.GetDouble(a), ts.GetDouble(b))
		},
		inexact: func(c *smt.Context, ts *verifier.TypeSystem, v *smt.Term) *smt.Term {
			return c.MkFPIsNaN(ts.GetDouble(v))
		}},
	{name: "bool", is: (*verifier.TypeSystem).IsBool,
		less: func(c *smt.Context, ts *verifier.TypeSystem, a, b *smt.Term) *smt.Term {
			return c.MkAnd(c.MkNot(ts.UnwrapBool(a)), ts.UnwrapBool(b))
		}},
	{name: "duration", is: (*verifier.TypeSystem).IsDuration, less: intLess((*verifier.TypeSystem).GetDuration)},
	{name: "timestamp", is: (*verifier.TypeSystem).IsTimestamp, less: intLess((*verifier.TypeSystem).GetTimestamp)},
	{name: "string", is: (*verifier.TypeSystem).IsString,
		less: func(c *smt.Context, ts *verifier.TypeSystem, a, b *smt.Term) *smt.Term {
			return c.MkStringLt(ts.GetString(a), ts.GetString(b))
		}},
	{name: "bytes", is: (*verifier.TypeSystem).IsBytes,
		less: func(c *smt.Context, ts *verifier.TypeSystem, a, b *smt.Term) *smt.Term {
			return c.MkStringLt(ts.GetBytes(a), ts.GetBytes(b))
		}},
}

// unrolled is the view of a list's first UnrollLimit elements.
type unrolled struct {
	elems, valid []*smt.Term
	// truncated holds when the list is longer than the unrolled prefix.
	truncated *smt.Term
}

func unroll(c *smt.Context, ts *verifier.TypeSystem, list *smt.Term) unrolled {
	seq := ts.GetSeq(ts.GetListRef(list))
	length := c.MkLength(seq)
	u := unrolled{truncated: c.MkGt(length, c.MkInt(UnrollLimit))}
	for i := 0; i < UnrollLimit; i++ {
		idx := c.MkInt(int64(i))
		u.elems = append(u.elems, c.MkNth(seq, idx))
		u.valid = append(u.valid, c.MkLt(idx, length))
	}
	return u
}

// inexact returns when the elements' kind or order isn't modeled exactly.
func (u unrolled) inexact(c *smt.Context, ts *verifier.TypeSystem, k elemKind) *smt.Term {
	parts := []*smt.Term{u.truncated}
	for i, e := range u.elems {
		bad := c.MkNot(k.is(ts, e))
		if k.inexact != nil {
			bad = c.MkOr(bad, k.inexact(c, ts, e))
		}
		parts = append(parts, c.MkAnd(u.valid[i], bad))
	}
	return c.MkOr(parts...)
}

type listOp func(c *smt.Context, ts *verifier.TypeSystem, sink func(*smt.Term), list *smt.Term) (v, approx *smt.Term)

func listsAxioms() []*verifier.FunctionAxiom {
	isSorted := newAxiom("isSorted")
	maxFn := newAxiom("max")
	minFn := newAxiom("min")
	sum := newAxiom("sum")
	for _, k := range elemKinds {
		k := k
		unaryOverload(isSorted, "list_"+k.name+"_is_sorted_bool", func(c *smt.Context, ts *verifier.TypeSystem, sink func(*smt.Term), list *smt.Term) (*smt.Term, *smt.Term) {
			u := unroll(c, ts, list)
			var ok []*smt.Term
			for i := 1; i < UnrollLimit; i++ {
				ok = append(ok, c.MkImplies(u.valid[i], c.MkNot(k.less(c, ts, u.elems[i], u.elems[i-1]))))
			}
			approx := u.inexact(c, ts, k)
			return freeWhen(c, ts, sink, "is_sorted", (*verifier.TypeSystem).IsBool, approx, ts.WrapBool(c.MkAnd(ok...)), list), approx
		})
		extreme := func(name string, preferNext func(c *smt.Context, ts *verifier.TypeSystem, cur, next *smt.Term) *smt.Term) listOp {
			return func(c *smt.Context, ts *verifier.TypeSystem, sink func(*smt.Term), list *smt.Term) (*smt.Term, *smt.Term) {
				u := unroll(c, ts, list)
				cur := u.elems[0]
				for i := 1; i < UnrollLimit; i++ {
					cur = c.MkITE(c.MkAnd(u.valid[i], preferNext(c, ts, cur, u.elems[i])), u.elems[i], cur)
				}
				approx := u.inexact(c, ts, k)
				exact := c.MkITE(u.valid[0], cur, ts.MkError())
				return freeWhen(c, ts, sink, name+"_"+k.name, k.is, approx, exact, list), approx
			}
		}
		unaryOverload(maxFn, "list_"+k.name+"_max_"+k.name, extreme("max", func(c *smt.Context, ts *verifier.TypeSystem, cur, next *smt.Term) *smt.Term {
			return k.less(c, ts, cur, next)
		}))
		unaryOverload(minFn, "list_"+k.name+"_min_"+k.name, extreme("min", func(c *smt.Context, ts *verifier.TypeSystem, cur, next *smt.Term) *smt.Term {
			return k.less(c, ts, next, cur)
		}))
	}
	for _, s := range summable {
		s := s
		unaryOverload(sum, "list_"+s.kind.name+"_sum_"+s.kind.name, func(c *smt.Context, ts *verifier.TypeSystem, sink func(*smt.Term), list *smt.Term) (*smt.Term, *smt.Term) {
			u := unroll(c, ts, list)
			acc := s.zero(c, ts)
			var overflow []*smt.Term
			for i, e := range u.elems {
				next := s.add(c, ts, acc, s.get(ts, e))
				if s.overflow != nil {
					overflow = append(overflow, c.MkAnd(u.valid[i], s.overflow(ts, next)))
				}
				acc = c.MkITE(u.valid[i], next, acc)
			}
			v := s.wrap(ts, acc)
			if len(overflow) > 0 {
				v = c.MkITE(c.MkOr(overflow...), ts.MkError(), v)
			}
			approx := u.inexact(c, ts, s.kind)
			return freeWhen(c, ts, sink, "sum_"+s.kind.name, s.kind.is, approx, v, list), approx
		})
	}

	index := func(last bool) func(c *smt.Context, ts *verifier.TypeSystem, sink func(*smt.Term), list, item *smt.Term) (*smt.Term, *smt.Term) {
		return func(c *smt.Context, ts *verifier.TypeSystem, sink func(*smt.Term), list, item *smt.Term) (*smt.Term, *smt.Term) {
			u := unroll(c, ts, list)
			out := c.MkInt(-1)
			approx := []*smt.Term{u.truncated}
			order := make([]int, UnrollLimit)
			for i := range order {
				order[i] = UnrollLimit - 1 - i // the first match wins
				if last {
					order[i] = i // the last match wins
				}
			}
			for _, i := range order {
				out = c.MkITE(c.MkAnd(u.valid[i], ts.StructuralEquality(u.elems[i], item)), c.MkInt(int64(i)), out)
			}
			for i, e := range u.elems {
				approx = append(approx, c.MkAnd(u.valid[i], inexactEquality(c, ts, e, item)))
			}
			name := "index_of"
			if last {
				name = "last_index_of"
			}
			a := c.MkOr(approx...)
			return freeWhen(c, ts, sink, name, (*verifier.TypeSystem).IsInt, a, ts.WrapInt(out), list, item), a
		}
	}
	indexOf := newAxiom("indexOf")
	binaryOverload(indexOf, "list_a_index_of_int", index(false))
	lastIndexOf := newAxiom("lastIndexOf")
	binaryOverload(lastIndexOf, "list_a_last_index_of_int", index(true))
	return []*verifier.FunctionAxiom{isSorted, sum, maxFn, minFn, indexOf, lastIndexOf}
}

// inexactEquality holds when CEL equality of a and b may differ from the
// equality of their terms: doubles (NaN, signed zeros), int against uint,
// and aggregates.
func inexactEquality(c *smt.Context, ts *verifier.TypeSystem, a, b *smt.Term) *smt.Term {
	aggregate := func(v *smt.Term) *smt.Term {
		return c.MkOr(ts.IsDouble(v), ts.IsList(v), ts.IsMap(v), ts.IsMessage(v), ts.IsOptional(v))
	}
	mixed := c.MkOr(c.MkAnd(ts.IsInt(a), ts.IsUint(b)), c.MkAnd(ts.IsUint(a), ts.IsInt(b)))
	return c.MkOr(aggregate(a), aggregate(b), mixed)
}

type summableKind struct {
	kind     elemKind
	get      func(ts *verifier.TypeSystem, v *smt.Term) *smt.Term
	wrap     func(ts *verifier.TypeSystem, v *smt.Term) *smt.Term
	zero     func(c *smt.Context, ts *verifier.TypeSystem) *smt.Term
	add      func(c *smt.Context, ts *verifier.TypeSystem, a, b *smt.Term) *smt.Term
	overflow func(ts *verifier.TypeSystem, v *smt.Term) *smt.Term
}

func intAdd(c *smt.Context, _ *verifier.TypeSystem, a, b *smt.Term) *smt.Term { return c.MkAdd(a, b) }
func intZero(c *smt.Context, _ *verifier.TypeSystem) *smt.Term                { return c.MkInt(0) }

var summable = []summableKind{
	{kind: elemKinds[0], get: (*verifier.TypeSystem).GetInt, wrap: (*verifier.TypeSystem).WrapInt, zero: intZero, add: intAdd,
		overflow: (*verifier.TypeSystem).CheckIntOverflow},
	{kind: elemKinds[1], get: (*verifier.TypeSystem).GetUint, wrap: (*verifier.TypeSystem).WrapUint, zero: intZero, add: intAdd,
		overflow: (*verifier.TypeSystem).CheckUintOverflow},
	{kind: elemKinds[2], get: (*verifier.TypeSystem).GetDouble, wrap: (*verifier.TypeSystem).WrapDouble,
		zero: func(c *smt.Context, ts *verifier.TypeSystem) *smt.Term { return ts.MkFpDouble(0) },
		add: func(c *smt.Context, _ *verifier.TypeSystem, a, b *smt.Term) *smt.Term {
			return c.MkFPAdd(c.MkFPRoundNearestTiesToEven(), a, b)
		}},
	{kind: elemKinds[4], get: (*verifier.TypeSystem).GetDuration, wrap: (*verifier.TypeSystem).WrapDuration, zero: intZero, add: intAdd,
		overflow: (*verifier.TypeSystem).CheckDurationOverflow},
}

// freeWhen returns exact unless approx holds, and otherwise an uninterpreted
// value of the arguments (of the result kind, or an error), so that results
// the unrolling doesn't determine stay unconstrained.
func freeWhen(c *smt.Context, ts *verifier.TypeSystem, sink func(*smt.Term), name string,
	is func(*verifier.TypeSystem, *smt.Term) *smt.Term, approx, exact *smt.Term, args ...*smt.Term) *smt.Term {
	if approx.IsFalse() {
		return exact
	}
	domain := make([]*smt.Sort, len(args))
	for i := range args {
		domain[i] = ts.CelValueSort()
	}
	free := c.MkApp(fn(ts, "lists_"+name, ts.CelValueSort(), domain...), args...)
	sink(c.MkOr(is(ts, free), ts.IsError(free)))
	return c.MkITE(approx, free, exact)
}
