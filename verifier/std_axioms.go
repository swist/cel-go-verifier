package verifier

import (
	"fmt"
	"math"

	"cel.dev/cel-go/common/types"

	"github.com/swist/cel-go-verifier/smt"
)

// StandardAxioms returns the axioms of CEL's standard library, the optional
// library and cel.@mapInsert.
func StandardAxioms() []*FunctionAxiom {
	var out []*FunctionAxiom
	out = append(out,
		addAxiom(), subtractAxiom(), multiplyAxiom(), divideAxiom(), moduloAxiom(), negateAxiom(),
		mapInsertAxiom(), typeAxiom(), inAxiom(),
		lessAxiom(), lessEqualsAxiom(), greaterAxiom(), greaterEqualsAxiom(), sizeAxiom())
	out = append(out, optionalAxioms()...)
	out = append(out, stringAxioms()...)
	out = append(out, typeConversionAxioms()...)
	return out
}

func std(name string) *FunctionAxiom {
	d, ok := standardDecls[name]
	if !ok {
		panic("verifier: no standard declaration for " + name)
	}
	return NewFunctionAxiom(d)
}

type intGetter func(*TypeSystem, *smt.Term) *smt.Term

var (
	getInt       intGetter = (*TypeSystem).GetInt
	getUint      intGetter = (*TypeSystem).GetUint
	getTimestamp intGetter = (*TypeSystem).GetTimestamp
	getDuration  intGetter = (*TypeSystem).GetDuration
	wrapInt      intGetter = (*TypeSystem).WrapInt
	wrapUint     intGetter = (*TypeSystem).WrapUint
	wrapTs       intGetter = (*TypeSystem).WrapTimestamp
	wrapDur      intGetter = (*TypeSystem).WrapDuration
	intOverflow  intGetter = (*TypeSystem).CheckIntOverflow
	tsOverflow   intGetter = (*TypeSystem).CheckTimestampOverflow
	durOverflow  intGetter = (*TypeSystem).CheckDurationOverflow
)

func arithTranslator(op func(c *smt.Context, a, b *smt.Term) *smt.Term, left, right, wrap, overflow intGetter) BinaryTranslator {
	return func(c *smt.Context, ts *TypeSystem, _ func(*smt.Term), l, r *smt.Term) (*smt.Term, bool) {
		a1, a2 := left(ts, l), right(ts, r)
		res := op(c, a1, a2)
		return ts.WithRuntimeError(wrap(ts, res), overflow(ts, res)), true
	}
}

func uintArith(op func(c *smt.Context, a, b *smt.Term) *smt.Term) BinaryTranslator {
	return func(c *smt.Context, ts *TypeSystem, _ func(*smt.Term), l, r *smt.Term) (*smt.Term, bool) {
		a1, a2 := ts.GetUint(l), ts.GetUint(r)
		res := ts.WrapUint(op(c, a1, a2))
		return ts.WithRuntimeError(res, ts.CheckUintOverflow(op(c, a1, a2))), true
	}
}

func fpArith(op func(c *smt.Context, rm, a, b *smt.Term) *smt.Term) BinaryTranslator {
	return func(c *smt.Context, ts *TypeSystem, _ func(*smt.Term), l, r *smt.Term) (*smt.Term, bool) {
		return ts.WrapDouble(op(c, c.MkFPRoundNearestTiesToEven(), ts.GetDouble(l), ts.GetDouble(r))), true
	}
}

func add(c *smt.Context, a, b *smt.Term) *smt.Term { return c.MkAdd(a, b) }
func sub(c *smt.Context, a, b *smt.Term) *smt.Term { return c.MkSub(a, b) }
func mul(c *smt.Context, a, b *smt.Term) *smt.Term { return c.MkMul(a, b) }

func addAxiom() *FunctionAxiom {
	return std("_+_").
		Binary("add_int64", arithTranslator(add, getInt, getInt, wrapInt, intOverflow)).
		Binary("add_timestamp_duration", arithTranslator(add, getTimestamp, getDuration, wrapTs, tsOverflow)).
		Binary("add_duration_timestamp", arithTranslator(add, getDuration, getTimestamp, wrapTs, tsOverflow)).
		Binary("add_duration_duration", arithTranslator(add, getDuration, getDuration, wrapDur, durOverflow)).
		Binary("add_uint64", uintArith(add)).
		Binary("add_double", fpArith((*smt.Context).MkFPAdd)).
		Binary("add_string", func(c *smt.Context, ts *TypeSystem, _ func(*smt.Term), l, r *smt.Term) (*smt.Term, bool) {
			return ts.WrapString(ts.MkConcatSafe(ts.GetString(l), ts.GetString(r))), true
		}).
		Binary("add_bytes", func(c *smt.Context, ts *TypeSystem, _ func(*smt.Term), l, r *smt.Term) (*smt.Term, bool) {
			return ts.WrapBytes(ts.MkConcatSafe(ts.GetBytes(l), ts.GetBytes(r))), true
		}).
		Binary("add_list", func(c *smt.Context, ts *TypeSystem, sink func(*smt.Term), l, r *smt.Term) (*smt.Term, bool) {
			ref1, ref2 := ts.GetListRef(l), ts.GetListRef(r)
			f := ts.InternFuncDecl("add_list", []*smt.Sort{ts.listRefSort, ts.listRefSort}, ts.listRefSort)
			res := c.MkApp(f, ref1, ref2)
			guard := c.MkAnd(ts.IsList(l), ts.IsList(r))
			sink(c.MkImplies(guard, c.MkEq(ts.GetSeq(res), ts.MkConcatSafe(ts.GetSeq(ref1), ts.GetSeq(ref2)))))
			return ts.WrapList(res), true
		})
}

func subtractAxiom() *FunctionAxiom {
	return std("_-_").
		Binary("subtract_int64", arithTranslator(sub, getInt, getInt, wrapInt, intOverflow)).
		Binary("subtract_timestamp_timestamp", arithTranslator(sub, getTimestamp, getTimestamp, wrapDur, durOverflow)).
		Binary("subtract_timestamp_duration", arithTranslator(sub, getTimestamp, getDuration, wrapTs, tsOverflow)).
		Binary("subtract_duration_duration", arithTranslator(sub, getDuration, getDuration, wrapDur, durOverflow)).
		Binary("subtract_uint64", uintArith(sub)).
		Binary("subtract_double", fpArith((*smt.Context).MkFPSub))
}

func multiplyAxiom() *FunctionAxiom {
	return std("_*_").
		Binary("multiply_int64", func(c *smt.Context, ts *TypeSystem, _ func(*smt.Term), l, r *smt.Term) (*smt.Term, bool) {
			a1, a2 := ts.GetInt(l), ts.GetInt(r)
			return ts.WithRuntimeError(ts.WrapInt(c.MkMul(a1, a2)), ts.CheckIntOverflow(c.MkMul(a1, a2))), true
		}).
		Binary("multiply_uint64", uintArith(mul)).
		Binary("multiply_double", fpArith((*smt.Context).MkFPMul))
}

// mkTruncatedDiv divides rounding toward zero, as CEL does (Z3's div is Euclidean).
func mkTruncatedDiv(c *smt.Context, a, b *smt.Term) *smt.Term {
	zero := c.MkInt(0)
	aNeg, bNeg := c.MkLt(a, zero), c.MkLt(b, zero)
	absA := c.MkITE(aNeg, c.MkUnaryMinus(a), a)
	absB := c.MkITE(bNeg, c.MkUnaryMinus(b), b)
	divAbs := c.MkDiv(absA, absB)
	return c.MkITE(c.MkXor(aNeg, bNeg), c.MkUnaryMinus(divAbs), divAbs)
}

// mkTruncatedMod is a - (a / b) * b with truncated division.
func mkTruncatedMod(c *smt.Context, a, b *smt.Term) *smt.Term {
	return c.MkSub(a, c.MkMul(mkTruncatedDiv(c, a, b), b))
}

func divideAxiom() *FunctionAxiom {
	return std("_/_").
		Binary("divide_int64", func(c *smt.Context, ts *TypeSystem, _ func(*smt.Term), l, r *smt.Term) (*smt.Term, bool) {
			a1, a2 := ts.GetInt(l), ts.GetInt(r)
			div := mkTruncatedDiv(c, a1, a2)
			return ts.WithRuntimeError(ts.WrapInt(div), c.MkEq(a2, c.MkInt(0)), ts.CheckIntOverflow(div)), true
		}).
		Binary("divide_uint64", func(c *smt.Context, ts *TypeSystem, _ func(*smt.Term), l, r *smt.Term) (*smt.Term, bool) {
			a1, a2 := ts.GetUint(l), ts.GetUint(r)
			return ts.WithRuntimeError(ts.WrapUint(c.MkDiv(a1, a2)), c.MkEq(a2, c.MkInt(0))), true
		}).
		Binary("divide_double", fpArith((*smt.Context).MkFPDiv))
}

func moduloAxiom() *FunctionAxiom {
	return std("_%_").
		Binary("modulo_int64", func(c *smt.Context, ts *TypeSystem, _ func(*smt.Term), l, r *smt.Term) (*smt.Term, bool) {
			a1, a2 := ts.GetInt(l), ts.GetInt(r)
			return ts.WithRuntimeError(ts.WrapInt(mkTruncatedMod(c, a1, a2)), c.MkEq(a2, c.MkInt(0))), true
		}).
		Binary("modulo_uint64", func(c *smt.Context, ts *TypeSystem, _ func(*smt.Term), l, r *smt.Term) (*smt.Term, bool) {
			a1, a2 := ts.GetUint(l), ts.GetUint(r)
			return ts.WithRuntimeError(ts.WrapUint(c.MkMod(a1, a2)), c.MkEq(a2, c.MkInt(0))), true
		})
}

func negateAxiom() *FunctionAxiom {
	return std("-_").
		Unary("negate_int64", func(c *smt.Context, ts *TypeSystem, _ func(*smt.Term), arg *smt.Term) (*smt.Term, bool) {
			a := ts.GetInt(arg)
			return ts.WithRuntimeError(ts.WrapInt(c.MkUnaryMinus(a)), ts.CheckIntOverflow(c.MkUnaryMinus(a))), true
		}, false).
		Unary("negate_double", func(c *smt.Context, ts *TypeSystem, _ func(*smt.Term), arg *smt.Term) (*smt.Term, bool) {
			return ts.WrapDouble(c.MkFPNeg(ts.GetDouble(arg))), true
		}, false)
}

func mapInsertAxiom() *FunctionAxiom {
	return std("cel.@mapInsert").
		Ternary("@mapInsert_map_key_value", func(c *smt.Context, ts *TypeSystem, sink func(*smt.Term), m, k, v *smt.Term) (*smt.Term, bool) {
			isMap := ts.IsMap(m)
			validKey := c.MkOr(ts.IsString(k), ts.IsInt(k), ts.IsUint(k), ts.IsBool(k))
			guard := c.MkAnd(isMap, validKey)
			newRef := ts.MkMapRefConst("mapInsertRef")
			oldRef := ts.GetMapRef(m)
			oldValues, oldPresence := ts.GetMapValues(oldRef), ts.GetMapPresence(oldRef)
			newValues := c.MkStore(oldValues, k, v)
			newPresence := c.MkStore(oldPresence, k, c.MkTrue())
			present := c.MkSelect(oldPresence, k)
			oldKeys := ts.GetMapKeys(oldRef)
			newKeys := c.MkITE(present, oldKeys, ts.MkConcatSafe(oldKeys, c.MkUnit(k)))
			sink(c.MkImplies(guard, c.MkEq(ts.GetMapValues(newRef), newValues)))
			sink(c.MkImplies(guard, c.MkEq(ts.GetMapPresence(newRef), newPresence)))
			sink(c.MkImplies(guard, c.MkEq(ts.GetMapKeys(newRef), newKeys)))
			return c.MkITE(guard, ts.WrapMap(newRef), ts.MkError()), true
		})
}

func typeAxiom() *FunctionAxiom {
	return std("type").Overload("type", func(c *smt.Context, ts *TypeSystem, _ func(*smt.Term), args, approx []*smt.Term) (OverloadResult, bool) {
		v := args[0]
		res := NewSwitch(c).
			Case(ts.IsStruct(v), ts.WrapString(ts.GetMsgTypeName(ts.GetMessageRef(v)))).
			Case(ts.IsOptional(v), ts.MkString("optional_type")).
			Case(ts.IsNull(v), ts.MkString("null_type")).
			Case(ts.IsTimestamp(v), ts.MkString("google.protobuf.Timestamp")).
			Case(ts.IsDuration(v), ts.MkString("google.protobuf.Duration")).
			Case(ts.IsMap(v), ts.MkString("map")).
			Case(ts.IsList(v), ts.MkString("list")).
			Case(ts.IsBytes(v), ts.MkString("bytes")).
			Case(ts.IsString(v), ts.MkString("string")).
			Case(ts.IsDouble(v), ts.MkString("double")).
			Case(ts.IsUint(v), ts.MkString("uint")).
			Case(ts.IsInt(v), ts.MkString("int")).
			Case(ts.IsBool(v), ts.MkString("bool")).
			Build(ts.MkError())
		// An approximate argument may have a different kind (or be an error) at runtime.
		return OverloadResult{res, approx[0]}, true
	})
}

func inAxiom() *FunctionAxiom {
	return std("@in").
		Binary("in_list", func(c *smt.Context, ts *TypeSystem, _ func(*smt.Term), lhs, rhs *smt.Term) (*smt.Term, bool) {
			seq := ts.GetSeq(ts.GetListRef(rhs))
			structContains := c.MkContains(seq, c.MkUnit(lhs))
			isDouble := ts.IsDouble(lhs)
			fp := ts.GetDouble(lhs)
			isNaN := c.MkFPIsNaN(fp)
			isZero := c.MkFPIsZero(fp)
			posZero := ts.WrapDouble(ts.MkFpDouble(0.0))
			negZero := ts.WrapDouble(ts.MkFpDouble(math.Copysign(0, -1)))
			intZero := ts.WrapInt(c.MkInt(0))
			uintZero := ts.WrapUint(c.MkInt(0))
			containsAnyZero := c.MkOr(
				c.MkContains(seq, c.MkUnit(posZero)),
				c.MkContains(seq, c.MkUnit(negZero)),
				c.MkContains(seq, c.MkUnit(intZero)),
				c.MkContains(seq, c.MkUnit(uintZero)))
			doubleInList := c.MkITE(isNaN, c.MkFalse(), c.MkITE(isZero, containsAnyZero, structContains))
			isInt, isUint := ts.IsInt(lhs), ts.IsUint(lhs)
			isIntOrUint := c.MkOr(isInt, isUint)
			intVal := c.MkITE(isInt, ts.GetInt(lhs), ts.GetUint(lhs))
			isIntZero := c.MkEq(intVal, c.MkInt(0))
			containsIntOrUint := c.MkOr(
				c.MkAnd(c.MkNot(ts.CheckIntOverflow(intVal)), c.MkContains(seq, c.MkUnit(ts.WrapInt(intVal)))),
				c.MkAnd(c.MkNot(ts.CheckUintOverflow(intVal)), c.MkContains(seq, c.MkUnit(ts.WrapUint(intVal)))))
			intInList := c.MkITE(isIntZero, containsAnyZero, containsIntOrUint)
			match := c.MkITE(isDouble, doubleInList, c.MkITE(isIntOrUint, intInList, structContains))
			return ts.WrapBool(match), true
		}).
		Binary("in_map", func(c *smt.Context, ts *TypeSystem, _ func(*smt.Term), lhs, rhs *smt.Term) (*smt.Term, bool) {
			return ts.WrapBool(ts.HasEqualKey(rhs, lhs)), true
		})
}

type cmpKind int

const (
	cmpLt cmpKind = iota
	cmpLe
	cmpGt
	cmpGe
)

// comparisonAxiom builds <, <=, > or >=. The overloads are added in the order of the Java axioms.
func comparisonAxiom(name, prefix string, k cmpKind) *FunctionAxiom {
	f := std(name)
	wrap := func(fn func(c *smt.Context, ts *TypeSystem, l, r *smt.Term) *smt.Term) BinaryTranslator {
		return func(c *smt.Context, ts *TypeSystem, _ func(*smt.Term), l, r *smt.Term) (*smt.Term, bool) {
			return ts.WrapBool(fn(c, ts, l, r)), true
		}
	}
	arith := func(c *smt.Context, a, b *smt.Term) *smt.Term {
		switch k {
		case cmpLt:
			return c.MkLt(a, b)
		case cmpLe:
			return c.MkLe(a, b)
		case cmpGt:
			return c.MkGt(a, b)
		}
		return c.MkGe(a, b)
	}
	fpCmp := func(c *smt.Context, a, b *smt.Term) *smt.Term {
		switch k {
		case cmpLt:
			return c.MkFPLt(a, b)
		case cmpLe:
			return c.MkFPLEq(a, b)
		case cmpGt:
			return c.MkFPGt(a, b)
		}
		return c.MkFPGEq(a, b)
	}
	strCmp := func(c *smt.Context, a, b *smt.Term) *smt.Term {
		switch k {
		case cmpLt:
			return c.MkStringLt(a, b)
		case cmpLe:
			return c.MkStringLe(a, b)
		case cmpGt:
			return c.MkStringLt(b, a)
		}
		return c.MkStringLe(b, a)
	}
	boolCmp := func(c *smt.Context, ts *TypeSystem, l, r *smt.Term) *smt.Term {
		a, b := ts.UnwrapBool(l), ts.UnwrapBool(r)
		switch k {
		case cmpLt:
			return c.MkAnd(c.MkNot(a), b)
		case cmpLe:
			return c.MkImplies(a, b)
		case cmpGt:
			return c.MkAnd(a, c.MkNot(b))
		}
		return c.MkImplies(b, a)
	}
	// Mixed int/double comparisons, expressed through the type system's exact helpers.
	intDouble := func(get intGetter) func(c *smt.Context, ts *TypeSystem, l, r *smt.Term) *smt.Term {
		return func(c *smt.Context, ts *TypeSystem, l, r *smt.Term) *smt.Term {
			n, d := get(ts, l), ts.GetDouble(r)
			switch k {
			case cmpLt:
				return ts.IntLtDouble(n, d)
			case cmpLe:
				return ts.IntLeDouble(n, d)
			case cmpGt:
				return ts.DoubleLtInt(d, n)
			}
			return ts.DoubleLeInt(d, n)
		}
	}
	doubleInt := func(get intGetter) func(c *smt.Context, ts *TypeSystem, l, r *smt.Term) *smt.Term {
		return func(c *smt.Context, ts *TypeSystem, l, r *smt.Term) *smt.Term {
			d, n := ts.GetDouble(l), get(ts, r)
			switch k {
			case cmpLt:
				return ts.DoubleLtInt(d, n)
			case cmpLe:
				return ts.DoubleLeInt(d, n)
			case cmpGt:
				return ts.IntLtDouble(n, d)
			}
			return ts.IntLeDouble(n, d)
		}
	}
	same := func(get intGetter) func(c *smt.Context, ts *TypeSystem, l, r *smt.Term) *smt.Term {
		return func(c *smt.Context, ts *TypeSystem, l, r *smt.Term) *smt.Term { return arith(c, get(ts, l), get(ts, r)) }
	}
	mixed := func(gl, gr intGetter) func(c *smt.Context, ts *TypeSystem, l, r *smt.Term) *smt.Term {
		return func(c *smt.Context, ts *TypeSystem, l, r *smt.Term) *smt.Term { return arith(c, gl(ts, l), gr(ts, r)) }
	}
	id := func(s string) string { return prefix + "_" + s }
	return f.
		Binary(id("bool"), wrap(boolCmp)).
		Binary(id("int64"), wrap(same(getInt))).
		Binary(id("timestamp"), wrap(same(getTimestamp))).
		Binary(id("duration"), wrap(same(getDuration))).
		Binary(id("uint64"), wrap(same(getUint))).
		Binary(id("double"), wrap(func(c *smt.Context, ts *TypeSystem, l, r *smt.Term) *smt.Term {
			return fpCmp(c, ts.GetDouble(l), ts.GetDouble(r))
		})).
		Binary(id("string"), wrap(func(c *smt.Context, ts *TypeSystem, l, r *smt.Term) *smt.Term {
			return strCmp(c, ts.GetString(l), ts.GetString(r))
		})).
		Binary(id("bytes"), wrap(func(c *smt.Context, ts *TypeSystem, l, r *smt.Term) *smt.Term {
			return strCmp(c, ts.GetBytes(l), ts.GetBytes(r))
		})).
		Binary(id("int64_double"), wrap(intDouble(getInt))).
		Binary(id("uint64_double"), wrap(intDouble(getUint))).
		Binary(id("double_int64"), wrap(doubleInt(getInt))).
		Binary(id("double_uint64"), wrap(doubleInt(getUint))).
		Binary(id("int64_uint64"), wrap(mixed(getInt, getUint))).
		Binary(id("uint64_int64"), wrap(mixed(getUint, getInt)))
}

func lessAxiom() *FunctionAxiom          { return comparisonAxiom("_<_", "less", cmpLt) }
func lessEqualsAxiom() *FunctionAxiom    { return comparisonAxiom("_<=_", "less_equals", cmpLe) }
func greaterAxiom() *FunctionAxiom       { return comparisonAxiom("_>_", "greater", cmpGt) }
func greaterEqualsAxiom() *FunctionAxiom { return comparisonAxiom("_>=_", "greater_equals", cmpGe) }

const maxContainerSize = math.MaxInt32

func sizeAxiom() *FunctionAxiom {
	bounded := func(get func(ts *TypeSystem, v *smt.Term) *smt.Term) UnaryTranslator {
		return func(c *smt.Context, ts *TypeSystem, sink func(*smt.Term), v *smt.Term) (*smt.Term, bool) {
			length := c.MkLength(get(ts, v))
			sink(c.MkLe(length, c.MkInt(maxContainerSize)))
			return ts.WrapInt(length), true
		}
	}
	str := func(ts *TypeSystem, v *smt.Term) *smt.Term { return ts.GetString(v) }
	byt := func(ts *TypeSystem, v *smt.Term) *smt.Term { return ts.GetBytes(v) }
	lst := func(ts *TypeSystem, v *smt.Term) *smt.Term { return ts.GetSeq(ts.GetListRef(v)) }
	mp := func(ts *TypeSystem, v *smt.Term) *smt.Term { return ts.GetMapKeys(ts.GetMapRef(v)) }
	return std("size").
		Unary("size_string", bounded(str), false).
		Unary("string_size", bounded(str), false).
		Unary("size_bytes", bounded(byt), false).
		Unary("bytes_size", bounded(byt), false).
		Unary("size_list", bounded(lst), false).
		Unary("list_size", bounded(lst), false).
		Unary("size_map", bounded(mp), false).
		Unary("map_size", bounded(mp), false)
}

func isZeroValue(c *smt.Context, ts *TypeSystem, v *smt.Term) *smt.Term {
	return c.MkOr(
		ts.IsNull(v),
		c.MkAnd(ts.IsBool(v), c.MkEq(ts.UnwrapBool(v), c.MkFalse())),
		c.MkAnd(ts.IsInt(v), c.MkEq(ts.GetInt(v), c.MkInt(0))),
		c.MkAnd(ts.IsUint(v), c.MkEq(ts.GetUint(v), c.MkInt(0))),
		c.MkAnd(ts.IsDouble(v), c.MkFPIsZero(ts.GetDouble(v))),
		c.MkAnd(ts.IsTimestamp(v), c.MkEq(ts.GetTimestamp(v), c.MkInt(0))),
		c.MkAnd(ts.IsDuration(v), c.MkEq(ts.GetDuration(v), c.MkInt(0))),
		c.MkAnd(ts.IsString(v), c.MkEq(ts.GetString(v), c.MkString(""))),
		c.MkAnd(ts.IsBytes(v), c.MkEq(c.MkLength(ts.GetBytes(v)), c.MkInt(0))),
		c.MkAnd(ts.IsList(v), c.MkEq(c.MkLength(ts.GetSeq(ts.GetListRef(v))), c.MkInt(0))),
		c.MkAnd(ts.IsMap(v), c.MkEq(c.MkLength(ts.GetMapKeys(ts.GetMapRef(v))), c.MkInt(0))),
		c.MkAnd(ts.IsMessage(v), c.MkEq(ts.GetMsgPresence(ts.GetMessageRef(v)), c.MkConstArray(c.StringSort(), c.MkFalse()))))
}

func singleOverload(name string) string {
	d := standardDecls[name]
	if len(d.Overloads) != 1 {
		panic(fmt.Sprintf("verifier: expected 1 overload for %s, found %d", name, len(d.Overloads)))
	}
	return d.Overloads[0].ID
}

func optionalAxioms() []*FunctionAxiom {
	unary := func(name string, t UnaryTranslator) *FunctionAxiom { return std(name).Unary(singleOverload(name), t, false) }
	binary := func(name string, t BinaryTranslator) *FunctionAxiom { return std(name).Binary(singleOverload(name), t) }
	return []*FunctionAxiom{
		std("optional.none").Overload(singleOverload("optional.none"), func(c *smt.Context, ts *TypeSystem, _ func(*smt.Term), _, _ []*smt.Term) (OverloadResult, bool) {
			return OverloadResult{ts.MkOptionalNone(), c.MkFalse()}, true
		}),
		unary("optional.of", func(c *smt.Context, ts *TypeSystem, sink func(*smt.Term), v *smt.Term) (*smt.Term, bool) {
			ref := c.MkApp(ts.OptionalOfRefFunc(), v)
			sink(c.MkEq(ts.GetOptionalValue(ref), v))
			sink(ts.OptHasValue(ref))
			return ts.MkOptionalOf(ref), true
		}),
		unary("optional.ofNonZeroValue", func(c *smt.Context, ts *TypeSystem, sink func(*smt.Term), v *smt.Term) (*smt.Term, bool) {
			ref := c.MkApp(ts.OptionalOfRefFunc(), v)
			isZero := isZeroValue(c, ts, v)
			sink(c.MkImplies(c.MkNot(isZero), c.MkEq(ts.GetOptionalValue(ref), v)))
			sink(c.MkImplies(c.MkNot(isZero), ts.OptHasValue(ref)))
			return c.MkITE(isZero, ts.MkOptionalNone(), ts.MkOptionalOf(ref)), true
		}),
		unary("hasValue", func(c *smt.Context, ts *TypeSystem, _ func(*smt.Term), v *smt.Term) (*smt.Term, bool) {
			return ts.WrapBool(ts.OptHasValue(ts.GetOptionalRef(v))), true
		}),
		unary("value", func(c *smt.Context, ts *TypeSystem, _ func(*smt.Term), v *smt.Term) (*smt.Term, bool) {
			ref := ts.GetOptionalRef(v)
			return c.MkITE(ts.OptHasValue(ref), ts.GetOptionalValue(ref), ts.MkError()), true
		}),
		binary("orValue", func(c *smt.Context, ts *TypeSystem, _ func(*smt.Term), v, other *smt.Term) (*smt.Term, bool) {
			ref := ts.GetOptionalRef(v)
			return c.MkITE(ts.OptHasValue(ref), ts.GetOptionalValue(ref), other), true
		}),
		binary("or", func(c *smt.Context, ts *TypeSystem, _ func(*smt.Term), v, other *smt.Term) (*smt.Term, bool) {
			ref := ts.GetOptionalRef(v)
			return c.MkITE(ts.OptHasValue(ref), v, other), true
		}),
		binary("_?._", func(c *smt.Context, ts *TypeSystem, sink func(*smt.Term), operand, field *smt.Term) (*smt.Term, bool) {
			ref := ts.GetOptionalRef(operand)
			isOpt := ts.IsOptional(operand)
			hasValue := ts.OptHasValue(ref)
			actual := c.MkITE(isOpt, ts.GetOptionalValue(ref), operand)
			isMap, isMsg := ts.IsMap(actual), ts.IsMessage(actual)
			validTarget := c.MkOr(isMap, isMsg)
			msgField := ts.GetString(field)
			msgRef, mapRef := ts.GetMessageRef(actual), ts.GetMapRef(actual)
			presence := NewSwitch(c).
				Case(isMsg, c.MkSelect(ts.GetMsgPresence(msgRef), msgField)).
				Case(isMap, c.MkSelect(ts.GetMapPresence(mapRef), field)).
				Build(c.MkFalse())
			value := NewSwitch(c).
				Case(isMsg, c.MkSelect(ts.GetMsgValues(msgRef), msgField)).
				Case(isMap, c.MkSelect(ts.GetMapValues(mapRef), field)).
				Build(ts.MkError())
			notError := c.MkNot(c.MkEq(value, ts.MkError()))
			shouldEvaluate := c.MkITE(isOpt, hasValue, c.MkTrue())
			sink(c.MkImplies(MkAndFlattened(c, shouldEvaluate, validTarget, presence), notError))
			resRef := c.MkApp(ts.OptionalOfRefFunc(), value)
			sink(c.MkEq(ts.GetOptionalValue(resRef), value))
			sink(ts.OptHasValue(resRef))
			optResult := c.MkITE(presence, ts.MkOptionalOf(resRef), ts.MkOptionalNone())
			result := c.MkITE(validTarget, optResult, ts.MkError())
			return c.MkITE(c.MkAnd(isOpt, c.MkNot(hasValue)), ts.MkOptionalNone(), result), true
		}),
	}
}

func stringAxioms() []*FunctionAxiom {
	return []*FunctionAxiom{
		std("contains").Binary("contains_string", func(c *smt.Context, ts *TypeSystem, _ func(*smt.Term), s, sub *smt.Term) (*smt.Term, bool) {
			return ts.WrapBool(c.MkContains(ts.GetString(s), ts.GetString(sub))), true
		}),
		std("startsWith").Binary("starts_with_string", func(c *smt.Context, ts *TypeSystem, _ func(*smt.Term), s, pre *smt.Term) (*smt.Term, bool) {
			return ts.WrapBool(c.MkPrefixOf(ts.GetString(pre), ts.GetString(s))), true
		}),
		std("endsWith").Binary("ends_with_string", func(c *smt.Context, ts *TypeSystem, _ func(*smt.Term), s, suf *smt.Term) (*smt.Term, bool) {
			return ts.WrapBool(c.MkSuffixOf(ts.GetString(suf), ts.GetString(s))), true
		}),
	}
}

func identity(_ *smt.Context, _ *TypeSystem, _ func(*smt.Term), v *smt.Term) (*smt.Term, bool) {
	return v, true
}

// uninterpretedConversion leaves a conversion uninterpreted, constrained to its result type.
func uninterpretedConversion(fn, id string) OverloadTranslator {
	var result *types.Type
	for _, o := range standardDecls[fn].Overloads {
		if o.ID == id {
			result = o.Result
		}
	}
	return UninterpretedConversion(id, result, id == "string_to_double")
}

// UninterpretedConversion returns a translator that applies an uninterpreted
// function named id, constrained to a value of the result type or an error.
// Its results are never exact. Unless mayBeNaN, double results aren't NaN.
func UninterpretedConversion(id string, result *types.Type, mayBeNaN bool) OverloadTranslator {
	return func(c *smt.Context, ts *TypeSystem, sink func(*smt.Term), args, _ []*smt.Term) (OverloadResult, bool) {
		f := ts.InternFuncDecl(id, []*smt.Sort{ts.celValueSort}, ts.celValueSort)
		res := c.MkApp(f, args[0])
		switch result.Kind() {
		case types.IntKind:
			sink(c.MkOr(ts.IsInt(res), ts.IsError(res)))
			sink(c.MkImplies(ts.IsInt(res), c.MkNot(ts.CheckIntOverflow(ts.GetInt(res)))))
		case types.TimestampKind:
			sink(c.MkOr(ts.IsTimestamp(res), ts.IsError(res)))
			sink(c.MkImplies(ts.IsTimestamp(res), c.MkNot(ts.CheckTimestampOverflow(ts.GetTimestamp(res)))))
		case types.DurationKind:
			sink(c.MkOr(ts.IsDuration(res), ts.IsError(res)))
			sink(c.MkImplies(ts.IsDuration(res), c.MkNot(ts.CheckDurationOverflow(ts.GetDuration(res)))))
		case types.UintKind:
			sink(c.MkOr(ts.IsUint(res), ts.IsError(res)))
			sink(c.MkImplies(ts.IsUint(res), c.MkNot(ts.CheckUintOverflow(ts.GetUint(res)))))
		case types.DoubleKind:
			sink(c.MkOr(ts.IsDouble(res), ts.IsError(res)))
			if !mayBeNaN {
				sink(c.MkImplies(ts.IsDouble(res), c.MkNot(c.MkFPIsNaN(ts.GetDouble(res)))))
			}
		case types.StringKind:
			sink(c.MkOr(ts.IsString(res), ts.IsError(res)))
		case types.BytesKind:
			sink(c.MkOr(ts.IsBytes(res), ts.IsError(res)))
		case types.BoolKind:
			sink(c.MkOr(ts.IsBool(res), ts.IsError(res)))
		default:
			panic(fmt.Sprintf("verifier: unsupported uninterpreted conversion result type %v", result))
		}
		return OverloadResult{res, c.MkTrue()}, true
	}
}

func typeConversionAxioms() []*FunctionAxiom {
	u := uninterpretedConversion
	return []*FunctionAxiom{
		std("int").
			Unary("int64_to_int64", identity, false).
			Unary("uint64_to_int64", func(c *smt.Context, ts *TypeSystem, _ func(*smt.Term), arg *smt.Term) (*smt.Term, bool) {
				v := ts.GetUint(arg)
				return ts.WithRuntimeError(ts.WrapInt(v), c.MkGt(v, c.MkIntString(MaxInt64))), true
			}, false).
			Overload("double_to_int64", u("int", "double_to_int64")).
			Overload("string_to_int64", u("int", "string_to_int64")).
			Unary("timestamp_to_int64", func(c *smt.Context, ts *TypeSystem, _ func(*smt.Term), arg *smt.Term) (*smt.Term, bool) {
				return ts.WrapInt(c.MkDiv(ts.GetTimestamp(arg), c.MkInt(NanosPerSecond))), true
			}, false),
		std("uint").
			Unary("uint64_to_uint64", identity, false).
			Unary("int64_to_uint64", func(c *smt.Context, ts *TypeSystem, _ func(*smt.Term), arg *smt.Term) (*smt.Term, bool) {
				v := ts.GetInt(arg)
				return ts.WithRuntimeError(ts.WrapUint(v), c.MkLt(v, c.MkInt(0))), true
			}, false).
			Overload("double_to_uint64", u("uint", "double_to_uint64")).
			Overload("string_to_uint64", u("uint", "string_to_uint64")),
		std("double").
			Unary("double_to_double", identity, false).
			Overload("int64_to_double", u("double", "int64_to_double")).
			Overload("uint64_to_double", u("double", "uint64_to_double")).
			Overload("string_to_double", u("double", "string_to_double")),
		std("string").
			Unary("string_to_string", identity, false).
			Overload("int64_to_string", u("string", "int64_to_string")).
			Overload("uint64_to_string", u("string", "uint64_to_string")).
			Overload("double_to_string", u("string", "double_to_string")).
			Overload("bool_to_string", u("string", "bool_to_string")).
			Overload("bytes_to_string", u("string", "bytes_to_string")).
			Overload("timestamp_to_string", u("string", "timestamp_to_string")).
			Overload("duration_to_string", u("string", "duration_to_string")),
		std("bytes").
			Unary("bytes_to_bytes", identity, false).
			Overload("string_to_bytes", u("bytes", "string_to_bytes")),
		std("dyn").Unary("to_dyn", identity, false),
		std("duration").
			Unary("duration_to_duration", identity, false).
			Overload("string_to_duration", u("duration", "string_to_duration")),
		std("timestamp").
			Unary("timestamp_to_timestamp", identity, false).
			Overload("string_to_timestamp", u("timestamp", "string_to_timestamp")).
			Unary("int64_to_timestamp", func(c *smt.Context, ts *TypeSystem, _ func(*smt.Term), arg *smt.Term) (*smt.Term, bool) {
				nanos := c.MkMul(ts.GetInt(arg), c.MkInt(NanosPerSecond))
				return ts.WithRuntimeError(ts.WrapTimestamp(nanos), ts.CheckTimestampOverflow(nanos)), true
			}, false),
		std("bool").
			Unary("bool_to_bool", identity, false).
			Overload("string_to_bool", u("bool", "string_to_bool")),
	}
}
