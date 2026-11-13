package verifier

import (
	"fmt"
	"math"
	"math/big"
	"strconv"

	"cel.dev/cel-go/common/ast"
	"cel.dev/cel-go/common/operators"
	"cel.dev/cel-go/common/types"

	"github.com/swist/cel-go-verifier/smt"
)

// operatorTranslator maps CEL operators and axiomatized functions to Z3.
type operatorTranslator struct {
	x        *translationContext
	c        *smt.Context
	ts       *TypeSystem
	tcg      *typeConstraintGenerator
	registry *functionRegistry
	limit    int
}

func newOperatorTranslator(x *translationContext, r *functionRegistry) *operatorTranslator {
	return &operatorTranslator{x: x, c: x.c, ts: x.ts, tcg: x.tcg, registry: r, limit: x.unrollLimit}
}

var knownOperators = map[string]bool{
	operators.Conditional: true, operators.LogicalAnd: true, operators.LogicalOr: true,
	operators.LogicalNot: true, operators.Equals: true, operators.NotEquals: true,
	operators.Less: true, operators.LessEquals: true, operators.Greater: true, operators.GreaterEquals: true,
	operators.Add: true, operators.Subtract: true, operators.Multiply: true, operators.Divide: true,
	operators.Modulo: true, operators.Negate: true, operators.Index: true, operators.OptIndex: true,
	operators.OptSelect: true, operators.In: true, operators.OldIn: true, operators.NotStrictlyFalse: true,
	operators.OldNotStrictlyFalse: true, operators.Has: true, operators.All: true, operators.Exists: true,
	operators.ExistsOne: true, "existsOne": true, operators.Map: true, operators.Filter: true,
}

// translateFunctionCall translates an operator or axiomatized call; ok is false for uninterpreted calls.
func (o *operatorTranslator) translateFunctionCall(fn string, args []tv, e ast.Expr, a *ast.AST) (tv, bool) {
	c, ts := o.c, o.ts
	isOp := knownOperators[fn]
	z3Args := make([]*smt.Term, len(args))
	argApprox := make([]*smt.Term, len(args))
	for i, arg := range args {
		z3Args[i] = arg.z3
		argApprox[i] = arg.approx
	}
	var chain tv
	if isOp {
		chain = o.translateOperatorCall(fn, args, a)
	} else {
		chain = propagateStrict(ts, fn, ts.MkError(), nil, c.MkFalse(), args)
	}
	ref := a.ReferenceMap()[e.ID()]
	decl, ok := o.registry.decls[fn]
	if !ok {
		return chain, isOp
	}
	if ref != nil {
		for _, id := range ref.OverloadIDs {
			if _, ok := o.registry.translators[id]; !ok {
				return tv{}, false
			}
		}
	}
	matched := false
	cur := chain.z3
	curApprox := chain.approx
	for i := len(decl.Overloads) - 1; i >= 0; i-- {
		ov := decl.Overloads[i]
		if ref != nil && len(ref.OverloadIDs) > 0 && !contains(ref.OverloadIDs, ov.ID) {
			continue
		}
		if len(ov.Params) != len(args) {
			continue
		}
		t, ok := o.registry.translators[ov.ID]
		if !ok {
			continue
		}
		res, ok := t(c, ts, o.x.addConstraint, z3Args, argApprox)
		if !ok {
			continue
		}
		matched = true
		guards := make([]*smt.Term, len(z3Args))
		for i, z := range z3Args {
			guards[i] = o.mkTypeGuard(z, ov.Params[i])
		}
		guard := MkAndFlattened(c, guards...)
		cur = c.MkITE(guard, res.Value, cur)
		curApprox = c.MkITE(guard, o.attributeApproximation(fn, res.Approx, argApprox), curApprox)
	}
	if !matched {
		return chain, isOp
	}
	switch fn {
	case operators.In:
		curApprox = MkOrFlattened(c, curApprox, o.constrainInWitnessTypes(args[0], args[1], a))
	case operators.OptSelect:
		operand := z3Args[0]
		target := c.MkITE(ts.IsOptional(operand), ts.GetOptionalValue(ts.GetOptionalRef(operand)), operand)
		curApprox = MkOrFlattened(c, curApprox, o.x.isTruncatedMap(target))
	}
	return tv{ts.propagateErrorAndUnknown(fn, cur, z3Args, z3Args), nil, curApprox}, true
}

func contains(xs []string, s string) bool {
	for _, x := range xs {
		if x == s {
			return true
		}
	}
	return false
}

// attributeApproximation records the part of an overload's approximation it adds itself.
func (o *operatorTranslator) attributeApproximation(fn string, approx *smt.Term, argApprox []*smt.Term) *smt.Term {
	c := o.c
	var substitutable []*smt.Term
	for _, a := range argApprox {
		if !a.IsTrue() {
			substitutable = append(substitutable, a)
		}
	}
	own := o.x.recordCallApproximation(fn, c.Simplify(o.x.withoutApproximation(approx, substitutable)))
	inherited := MkAndFlattened(c, approx, MkOrFlattened(c, argApprox...))
	return MkOrFlattened(c, own, inherited)
}

// constrainInWitnessTypes constrains the values `in` may find in rhs to its
// guaranteed element type, and returns where the result stays approximate.
func (o *operatorTranslator) constrainInWitnessTypes(lhsTV, rhsTV tv, a *ast.AST) *smt.Term {
	c, ts := o.c, o.ts
	lhs, rhs := lhsTV.z3, rhsTV.z3
	rhsType := o.guaranteedType(rhsTV)
	switch rhsType.Kind() {
	case types.ListKind:
		intVal := c.MkITE(ts.IsInt(lhs), ts.GetInt(lhs), ts.GetUint(lhs))
		candidates := []*smt.Term{
			lhs, ts.WrapInt(intVal), ts.WrapUint(intVal),
			ts.MkDouble(0.0), ts.MkDouble(math.Copysign(0, -1)), ts.MkInt(0), ts.MkUint64(0),
		}
		elemType := listElemType(rhsType)
		seq := ts.GetSeq(ts.GetListRef(rhs))
		for _, cand := range candidates {
			contains := c.MkContains(seq, c.MkUnit(cand))
			o.x.addConstraint(c.MkImplies(c.MkAnd(ts.IsList(rhs), contains), o.tcg.forType(cand, elemType)))
		}
		if isConcrete(elemType) {
			return o.mayObserveTruncatedTypeConstraint(a, lhsTV)
		}
		return o.mayObserveTruncatedTypeConstraint(a, lhsTV, rhsTV)
	case types.MapKind:
		presence := ts.GetMapPresence(ts.GetMapRef(rhs))
		for _, k := range ts.equalKeys(lhs) {
			o.x.addConstraint(c.MkImplies(
				c.MkAnd(ts.IsMap(rhs), k.Cond, c.MkSelect(presence, k.Key)),
				o.tcg.forType(k.Key, mapKeyType(rhsType))))
		}
		return o.x.isTruncatedMap(rhs)
	}
	return MkOrFlattened(c, o.x.isTruncatedMap(rhs), o.mayObserveTruncatedTypeConstraint(a, lhsTV, rhsTV))
}

func (o *operatorTranslator) mkTypeGuard(arg *smt.Term, t *types.Type) *smt.Term {
	ts := o.ts
	switch t.Kind() {
	case types.ListKind:
		return ts.IsList(arg)
	case types.MapKind:
		return ts.IsMap(arg)
	case types.AnyKind, types.TypeParamKind, types.DynKind:
		return o.c.MkTrue()
	case types.IntKind:
		return ts.IsInt(arg)
	case types.TimestampKind:
		return ts.IsTimestamp(arg)
	case types.DurationKind:
		return ts.IsDuration(arg)
	case types.UintKind:
		return ts.IsUint(arg)
	case types.DoubleKind:
		return ts.IsDouble(arg)
	case types.BoolKind:
		return ts.IsBool(arg)
	case types.StringKind:
		return ts.IsString(arg)
	case types.BytesKind:
		return ts.IsBytes(arg)
	case types.StructKind:
		return ts.IsStruct(arg)
	case types.NullTypeKind:
		return ts.IsNull(arg)
	case types.OpaqueKind:
		if t.TypeName() == optionalTypeName {
			return ts.IsOptional(arg)
		}
	}
	panic(fmt.Sprintf("verifier: unsupported type for dynamic type guard: %v", t))
}

func (o *operatorTranslator) translateOperatorCall(op string, args []tv, a *ast.AST) tv {
	n := len(args)
	switch op {
	case operators.Negate, operators.LogicalNot, operators.NotStrictlyFalse, operators.OldNotStrictlyFalse:
		if n != 1 {
			panic(fmt.Sprintf("malformed AST: operator %s expects 1 argument, got %d", op, n))
		}
	case operators.Conditional:
		if n != 3 {
			panic(fmt.Sprintf("malformed AST: operator %s expects 3 arguments, got %d", op, n))
		}
	case operators.LogicalAnd, operators.LogicalOr:
		if n < 2 {
			panic(fmt.Sprintf("malformed AST: operator %s expects at least 2 arguments, got %d", op, n))
		}
	default:
		if n != 2 {
			panic(fmt.Sprintf("malformed AST: operator %s expects 2 arguments, got %d", op, n))
		}
	}
	ts := o.ts
	switch op {
	case operators.LogicalAnd:
		return o.translateLogicalAndOr(args, true)
	case operators.LogicalOr:
		return o.translateLogicalAndOr(args, false)
	case operators.LogicalNot:
		return o.translateLogicalNot(args, a)
	case operators.Negate:
		return o.translateNegate(args[0], a)
	case operators.Equals:
		return o.translateEquality(args[0], args[1], a, true)
	case operators.NotEquals:
		return o.translateEquality(args[0], args[1], a, false)
	case operators.Less, operators.Greater, operators.LessEquals, operators.GreaterEquals,
		operators.Add, operators.Subtract, operators.Multiply, operators.Divide, operators.Modulo,
		operators.In:
		// A type mismatch in an operator the axioms don't handle.
		return propagateStrictOp(ts, op, ts.MkError(), args...)
	case operators.Index:
		return o.translateIndex(args, a, false)
	case operators.OptIndex:
		return o.translateIndex(args, a, true)
	case operators.Conditional:
		return o.translateConditional(args, a)
	case operators.NotStrictlyFalse, operators.OldNotStrictlyFalse:
		return o.translateNotStrictlyFalse(args)
	}
	return propagateStrictOp(ts, op, ts.MkUnknown(), args...).
		withApproximation(o.c, o.x.recordCallApproximation(op, o.c.MkTrue()))
}

func (o *operatorTranslator) translateLogicalAndOr(args []tv, isAnd bool) tv {
	r := args[0]
	for _, b := range args[1:] {
		r = o.binaryLogical(r, b, isAnd)
	}
	return r
}

func (o *operatorTranslator) binaryLogical(a, b tv, isAnd bool) tv {
	c, ts := o.c, o.ts
	aIsBool, bIsBool := ts.IsBool(a.z3), ts.IsBool(b.z3)
	aTrue := c.MkAnd(aIsBool, ts.UnwrapBool(a.z3))
	bTrue := c.MkAnd(bIsBool, ts.UnwrapBool(b.z3))
	aFalse := c.MkAnd(aIsBool, c.MkNot(ts.UnwrapBool(a.z3)))
	bFalse := c.MkAnd(bIsBool, c.MkNot(ts.UnwrapBool(b.z3)))
	var hasMatch, aMatch, bMatch *smt.Term
	if isAnd {
		hasMatch, aMatch, bMatch = c.MkOr(aFalse, bFalse), aFalse, bFalse
	} else {
		hasMatch, aMatch, bMatch = c.MkOr(aTrue, bTrue), aTrue, bTrue
	}
	aUnk, bUnk := ts.IsUnknown(a.z3), ts.IsUnknown(b.z3)
	hasUnknown := c.MkOr(aUnk, bUnk)
	hasError := c.MkOr(c.MkNot(c.MkOr(aIsBool, ts.IsUnknown(a.z3))), c.MkNot(c.MkOr(bIsBool, ts.IsUnknown(b.z3))))
	hasSafeMatch := c.MkOr(c.MkAnd(aMatch, c.MkNot(a.approx)), c.MkAnd(bMatch, c.MkNot(b.approx)))
	opName := operators.LogicalOr
	if isAnd {
		opName = operators.LogicalAnd
	}
	var unknownResult *smt.Term
	if ts.isParameterizingUnknowns() {
		unknownResult = ts.mkParameterizedUnknown(opName, []*smt.Term{a.z3, b.z3})
	} else {
		unknownResult = c.MkITE(ts.IsUnknown(a.z3), a.z3, b.z3)
	}
	res := NewSwitch(c).
		Case(hasMatch, ts.MkBool(!isAnd)).
		Case(hasUnknown, unknownResult).
		Case(hasError, ts.MkError()).
		Build(ts.MkBool(isAnd))
	taint := MkAndFlattened(c, MkNotFlattened(c, hasSafeMatch), MkOrFlattened(c, a.approx, b.approx))
	return tv{res, nil, taint}
}

func (o *operatorTranslator) translateLogicalNot(args []tv, a *ast.AST) tv {
	c, ts := o.c, o.ts
	arg := args[0]
	t := exprType(a, arg.expr)
	base := ts.WrapBool(c.MkNot(ts.UnwrapBool(arg.z3)))
	if !isExactly(t, types.BoolType) {
		base = ts.WithRuntimeError(base, c.MkNot(ts.IsBool(arg.z3)))
	}
	return propagateStrictOp(ts, operators.LogicalNot, base, args...)
}

func (o *operatorTranslator) translateNegate(arg tv, a *ast.AST) tv {
	c, ts := o.c, o.ts
	t := exprType(a, arg.expr)
	z := arg.z3
	var res *smt.Term
	switch {
	case isExactly(t, types.IntType):
		neg := c.MkUnaryMinus(ts.GetInt(z))
		res = ts.WithRuntimeError(ts.WrapInt(neg), ts.CheckIntOverflow(neg))
	case isExactly(t, types.DoubleType):
		res = ts.WrapDouble(c.MkFPNeg(ts.GetDouble(z)))
	default:
		neg := c.MkUnaryMinus(ts.GetInt(z))
		intRes := ts.WithRuntimeError(ts.WrapInt(neg), ts.CheckIntOverflow(neg))
		dblRes := ts.WrapDouble(c.MkFPNeg(ts.GetDouble(z)))
		res = NewSwitch(c).Case(ts.IsInt(z), intRes).Case(ts.IsDouble(z), dblRes).Build(ts.MkError())
	}
	return propagateStrictOp(ts, operators.Negate, res, arg)
}

func (o *operatorTranslator) isNumeric(v *smt.Term) *smt.Term {
	return o.c.MkOr(o.ts.IsInt(v), o.ts.IsUint(v), o.ts.IsDouble(v))
}

type intRange struct{ min, max string }

func (o *operatorTranslator) numericEqualityWithConstant(sym *smt.Term, lit tv, symType *types.Type) *smt.Term {
	c, ts := o.c, o.ts
	var ir, ur *intRange
	var dv float64
	switch v := lit.constant().Value().(type) {
	case int64:
		s := strconv.FormatInt(v, 10)
		ir = &intRange{s, s}
		if v >= 0 {
			ur = &intRange{s, s}
		}
		dv = float64(v)
	case uint64:
		if int64(v) >= 0 {
			s := strconv.FormatInt(int64(v), 10)
			ir = &intRange{s, s}
		}
		s := strconv.FormatUint(v, 10)
		ur = &intRange{s, s}
		dv = float64(v)
	case float64:
		dv = v
		ir = matchingIntRange(v)
		ur = matchingUintRange(v)
	default:
		panic(fmt.Sprintf("verifier: unexpected numeric constant %v", v))
	}
	if isStaticallyKnown(symType) {
		switch symType.Kind() {
		case types.IntKind:
			return o.rangeExpr(ir, ts.GetInt(sym))
		case types.UintKind:
			return o.rangeExpr(ur, ts.GetUint(sym))
		case types.DoubleKind:
			return c.MkFPEq(ts.GetDouble(sym), ts.MkFpDouble(dv))
		}
	}
	intEq := o.rangeExpr(ir, ts.GetInt(sym))
	uintEq := o.rangeExpr(ur, ts.GetUint(sym))
	dblEq := c.MkFPEq(ts.GetDouble(sym), ts.MkFpDouble(dv))
	return NewSwitch(c).
		Case(ts.IsInt(sym), intEq).
		Case(ts.IsUint(sym), uintEq).
		Case(ts.IsDouble(sym), dblEq).
		Build(c.MkFalse())
}

func (o *operatorTranslator) rangeExpr(r *intRange, v *smt.Term) *smt.Term {
	c := o.c
	if r == nil {
		return c.MkFalse()
	}
	return c.MkAnd(c.MkGe(v, c.MkIntString(r.min)), c.MkLe(v, c.MkIntString(r.max)))
}

func isMathematicalInteger(v float64) bool {
	return !math.IsInf(v, 0) && !math.IsNaN(v) && v == math.RoundToEven(v)
}

// matchingIntRange returns the int64s equal to the double v.
func matchingIntRange(v float64) *intRange {
	if !isMathematicalInteger(v) || v < -twoTo63 || v > twoTo63 {
		return nil
	}
	lo := javaLong(v)
	for lo > math.MinInt64 && float64(lo-1) == v {
		lo--
	}
	hi := javaLong(v)
	for hi < math.MaxInt64 && float64(hi+1) == v {
		hi++
	}
	return &intRange{strconv.FormatInt(lo, 10), strconv.FormatInt(hi, 10)}
}

// javaLong converts like Java's (long) cast, saturating at the int64 bounds.
func javaLong(v float64) int64 {
	if v >= twoTo63 {
		return math.MaxInt64
	}
	if v <= -twoTo63 {
		return math.MinInt64
	}
	return int64(v)
}

// matchingUintRange returns the uint64s equal to the double v.
func matchingUintRange(v float64) *intRange {
	if !isMathematicalInteger(v) || v < 0 || v > twoTo64 {
		return nil
	}
	var u uint64
	if v < twoTo63 {
		u = uint64(int64(v))
	} else {
		u = uint64(javaLong(v-twoTo63)) ^ (1 << 63)
	}
	toF := func(x uint64) float64 { f, _ := new(big.Float).SetUint64(x).Float64(); return f }
	lo := u
	for lo != 0 && toF(lo-1) == v {
		lo--
	}
	hi := u
	for hi != math.MaxUint64 && toF(hi+1) == v {
		hi++
	}
	return &intRange{strconv.FormatUint(lo, 10), strconv.FormatUint(hi, 10)}
}

func (o *operatorTranslator) numericEquality(a0, a1 tv, a *ast.AST) *smt.Term {
	if a0.isNumericConstant() {
		return o.numericEqualityWithConstant(a1.z3, a0, exprType(a, a1.expr))
	}
	if a1.isNumericConstant() {
		return o.numericEqualityWithConstant(a0.z3, a1, exprType(a, a0.expr))
	}
	t0, t1 := exprType(a, a0.expr), exprType(a, a1.expr)
	if isStaticallyKnown(t0) && isStaticallyKnown(t1) && t0.Kind() == t1.Kind() {
		return o.staticNumericEquality(a0.z3, t0, a1.z3)
	}
	return o.dynamicNumericEquality(a0.z3, a1.z3)
}

func (o *operatorTranslator) staticNumericEquality(z0 *smt.Term, t0 *types.Type, z1 *smt.Term) *smt.Term {
	c, ts := o.c, o.ts
	switch t0.Kind() {
	case types.IntKind:
		return c.MkEq(ts.GetInt(z0), ts.GetInt(z1))
	case types.UintKind:
		return c.MkEq(ts.GetUint(z0), ts.GetUint(z1))
	case types.DoubleKind:
		return c.MkFPEq(ts.GetDouble(z0), ts.GetDouble(z1))
	}
	return c.MkFalse()
}

func (o *operatorTranslator) dynamicNumericEquality(z0, z1 *smt.Term) *smt.Term {
	c, ts := o.c, o.ts
	isIU0 := c.MkOr(ts.IsInt(z0), ts.IsUint(z0))
	isIU1 := c.MkOr(ts.IsInt(z1), ts.IsUint(z1))
	bothIU := c.MkAnd(isIU0, isIU1)
	v0 := c.MkITE(ts.IsInt(z0), ts.GetInt(z0), c.MkITE(ts.IsUint(z0), ts.GetUint(z0), c.MkInt(0)))
	v1 := c.MkITE(ts.IsInt(z1), ts.GetInt(z1), c.MkITE(ts.IsUint(z1), ts.GetUint(z1), c.MkInt(0)))
	bothDouble := c.MkAnd(ts.IsDouble(z0), ts.IsDouble(z1))
	iuAndDouble := c.MkAnd(isIU0, ts.IsDouble(z1))
	doubleAndIU := c.MkAnd(ts.IsDouble(z0), isIU1)
	fp0, fp1 := o.guardedDouble(z0), o.guardedDouble(z1)
	return NewSwitch(c).
		Case(bothIU, c.MkEq(v0, v1)).
		Case(bothDouble, c.MkFPEq(ts.GetDouble(z0), ts.GetDouble(z1))).
		Case(iuAndDouble, ts.intEqDouble(v0, fp1)).
		Case(doubleAndIU, ts.intEqDouble(v1, fp0)).
		Build(c.MkFalse())
}

func (o *operatorTranslator) guardedDouble(z *smt.Term) *smt.Term {
	return o.c.MkITE(o.ts.IsDouble(z), o.ts.GetDouble(z), o.ts.MkFpDouble(0.0))
}

func hasOptionalElements(v tv) bool {
	return v.isLiteral(ast.ListKind) && len(v.expr.AsList().OptionalIndices()) > 0
}

// unrollListEquality compares against a list literal element-wise.
func (o *operatorTranslator) unrollListEquality(la, lb tv, a *ast.AST, taints *[]*smt.Term) *smt.Term {
	c, ts := o.c, o.ts
	lit := lb.expr
	if la.isLiteral(ast.ListKind) {
		lit = la.expr
	}
	t0, t1 := o.guaranteedType(la), o.guaranteedType(lb)
	seq0 := ts.GetSeq(ts.GetListRef(la.z3))
	seq1 := ts.GetSeq(ts.GetListRef(lb.z3))
	eqs := []*smt.Term{c.MkEq(c.MkLength(seq0), c.MkLength(seq1))}
	size := len(lit.AsList().Elements())
	for i := 0; i < size; i++ {
		idx := c.MkInt(int64(i))
		e0, e1 := c.MkNth(seq0, idx), c.MkNth(seq1, idx)
		if !la.isLiteral(ast.ListKind) && !hasConcreteElements(t0) {
			o.x.constrainValidValue(c.MkAnd(ts.IsList(la.z3), c.MkLt(idx, c.MkLength(seq0))), e0)
		}
		if !lb.isLiteral(ast.ListKind) && !hasConcreteElements(t1) {
			o.x.constrainValidValue(c.MkAnd(ts.IsList(lb.z3), c.MkLt(idx, c.MkLength(seq1))), e1)
		}
		if i >= o.limit {
			o.constrainListElement(seq0, idx, e0, t0)
			o.constrainListElement(seq1, idx, e1, t1)
		}
		ea := tv{e0, la.listElementAt(i), la.approx}
		eb := tv{e1, lb.listElementAt(i), lb.approx}
		eq := o.translateEquality(ea, eb, a, true)
		eqs = append(eqs, c.MkAnd(ts.IsBool(eq.z3), ts.UnwrapBool(eq.z3)))
		*taints = append(*taints, eq.approx)
	}
	return MkAndFlattened(c, eqs...)
}

// unrollMapEquality compares against a map literal key by key.
func (o *operatorTranslator) unrollMapEquality(ma, mb tv, a *ast.AST, taints *[]*smt.Term) *smt.Term {
	c, ts := o.c, o.ts
	isLiteralA := ma.isLiteral(ast.MapKind) &&
		!(mb.isLiteral(ast.MapKind) && hasContainerLiteralValue(mb) && !hasContainerLiteralValue(ma))
	literal, other := mb, ma.z3
	if isLiteralA {
		literal, other = ma, mb.z3
	}
	isOtherMap := ts.IsMap(other)
	litRef := ts.GetMapRef(literal.z3)
	keys := ts.GetMapKeys(litRef)
	values := ts.GetMapValues(litRef)
	length := c.MkLength(keys)
	otherRef := ts.GetMapRef(other)
	otherKeys := ts.GetMapKeys(otherRef)
	eqs := []*smt.Term{c.MkEq(length, c.MkLength(otherKeys))}
	entries := literal.expr.AsMap().Entries()
	inEntryOrder := true
	for _, e := range entries {
		if e.AsMapEntry().IsOptional() {
			inEntryOrder = false
		}
	}
	for i, en := range entries {
		inBounds := c.MkLt(c.MkInt(int64(i)), length)
		key := c.Simplify(c.MkNth(keys, c.MkInt(int64(i))))
		eks := ts.equalKeys(key)
		hasKey := ts.hasEqualKey(other, eks)
		otherValue := ts.valueAtEqualKey(other, eks)
		o.x.constrainValidValue(c.MkAnd(isOtherMap, inBounds, hasKey), otherValue)
		value := c.MkSelect(values, key)
		valueAst := en.AsMapEntry().Value()
		isValueLiteral := inEntryOrder && isContainerLiteral(valueAst)
		var lhs tv
		if inEntryOrder {
			lhs = tv{value, valueAst, literal.approx}
		} else {
			lhs = tv{value, nil, literal.approx}
		}
		veq := o.translateEquality(lhs, tv{otherValue, nil, c.MkFalse()}, a, true)
		*taints = append(*taints, c.MkAnd(inBounds, veq.approx))
		if !isValueLiteral {
			*taints = append(*taints, o.x.recordApproximation(
				"comparisons of lists or maps nested in maps",
				MkAndFlattened(c, isOtherMap, inBounds, hasKey,
					c.MkOr(
						c.MkAnd(ts.IsList(value), ts.IsList(otherValue)),
						c.MkAnd(ts.IsMap(value), ts.IsMap(otherValue))))))
		}
		eqs = append(eqs, c.MkImplies(inBounds, c.MkAnd(hasKey, ts.IsBool(veq.z3), ts.UnwrapBool(veq.z3))))
	}
	presence := c.MkConstArray(ts.celValueSort, c.MkFalse())
	for j := range entries {
		ok := c.MkNth(otherKeys, c.MkInt(int64(j)))
		presence = c.MkITE(c.MkLt(c.MkInt(int64(j)), length), c.MkStore(presence, ok, c.MkTrue()), presence)
	}
	eqs = append(eqs, c.MkEq(ts.GetMapPresence(otherRef), presence))
	return MkAndFlattened(c, eqs...)
}

func (o *operatorTranslator) mapEqualityAtLiteralKeys(ma, mb tv) *smt.Term {
	c, ts := o.c, o.ts
	isLiteralA := ma.isLiteral(ast.MapKind)
	lit, oth := mb, ma
	if isLiteralA {
		lit, oth = ma, mb
	}
	litRef, otherRef := ts.GetMapRef(lit.z3), ts.GetMapRef(oth.z3)
	keys := ts.GetMapKeys(litRef)
	values := ts.GetMapValues(litRef)
	otherValues := ts.GetMapValues(otherRef)
	eqs := []*smt.Term{
		c.MkEq(c.MkLength(keys), c.MkLength(ts.GetMapKeys(otherRef))),
		c.MkEq(ts.GetMapPresence(litRef), ts.GetMapPresence(otherRef)),
	}
	size := len(lit.expr.AsMap().Entries())
	for i := 0; i < size; i++ {
		key := c.MkNth(keys, c.MkInt(int64(i)))
		eqs = append(eqs, c.MkImplies(
			c.MkLt(c.MkInt(int64(i)), c.MkLength(keys)),
			ts.StructuralEquality(c.MkSelect(values, key), c.MkSelect(otherValues, key))))
	}
	return MkAndFlattened(c, eqs...)
}

func hasContainerLiteralValue(m tv) bool {
	for _, e := range m.expr.AsMap().Entries() {
		if isContainerLiteral(e.AsMapEntry().Value()) {
			return true
		}
	}
	return false
}

func isContainerLiteral(e ast.Expr) bool { return e.Kind() == ast.ListKind || e.Kind() == ast.MapKind }

func (o *operatorTranslator) constrainListElement(seq, idx, elem *smt.Term, listType *types.Type) {
	if listType.Kind() == types.ListKind {
		c := o.c
		o.x.addConstraint(c.MkImplies(c.MkLt(idx, c.MkLength(seq)), o.tcg.forType(elem, listElemType(listType))))
	}
}

func (o *operatorTranslator) translateEquality(a0, a1 tv, a *ast.AST, isEquals bool) tv {
	c, ts := o.c, o.ts
	z0, z1 := a0.z3, a1.z3
	t0, t1 := exprType(a, a0.expr), exprType(a, a1.expr)
	var equality *smt.Term
	taints := []*smt.Term{o.mayObserveTruncatedTypeConstraint(a, a0, a1)}
	switch {
	case isNumericType(t0) && isNumericType(t1):
		equality = o.numericEquality(a0, a1, a)
	case t0.Kind() == types.ListKind && t1.Kind() == types.ListKind &&
		(a0.isLiteral(ast.ListKind) || a1.isLiteral(ast.ListKind)) &&
		!hasOptionalElements(a0) && !hasOptionalElements(a1):
		equality = o.unrollListEquality(a0, a1, a, &taints)
	case a0.isLiteral(ast.MapKind) || a1.isLiteral(ast.MapKind):
		var inner *smt.Term
		if typeEquals(t0, t1) && hasStructuralEquality(t0) {
			inner = o.mapEqualityAtLiteralKeys(a0, a1)
		} else {
			inner = o.unrollMapEquality(a0, a1, a, &taints)
		}
		equality = c.MkITE(c.MkAnd(ts.IsMap(z0), ts.IsMap(z1)), inner, ts.StructuralEquality(z0, z1))
	case isStaticallyKnown(t0) && isStaticallyKnown(t1):
		equality = ts.StructuralEquality(z0, z1)
	default:
		canBeNumeric0 := !isStaticallyKnown(t0) || isNumericType(t0)
		canBeNumeric1 := !isStaticallyKnown(t1) || isNumericType(t1)
		structural := ts.StructuralEquality(z0, z1)
		if (a0.isLiteral(ast.ListKind) || a1.isLiteral(ast.ListKind)) && !hasOptionalElements(a0) && !hasOptionalElements(a1) {
			structural = c.MkITE(c.MkAnd(ts.IsList(z0), ts.IsList(z1)), o.unrollListEquality(a0, a1, a, &taints), structural)
		}
		if canBeNumeric0 && canBeNumeric1 {
			bothNumeric := c.MkAnd(o.isNumeric(z0), o.isNumeric(z1))
			equality = c.MkITE(bothNumeric, o.numericEquality(a0, a1, a), structural)
		} else {
			equality = structural
		}
	}
	if !isEquals {
		equality = c.MkNot(equality)
	}
	opName := operators.NotEquals
	if isEquals {
		opName = operators.Equals
	}
	return propagateStrictOp(ts, opName, ts.WrapBool(equality), a0, a1).withApproximation(c, MkOrFlattened(c, taints...))
}

func (o *operatorTranslator) buildListIndex(lhs, rhs, guard *smt.Term, optional bool) *smt.Term {
	c, ts := o.c, o.ts
	seq := ts.GetSeq(ts.GetListRef(lhs))
	idx := ts.GetInt(rhs)
	inBounds := c.MkAnd(c.MkGe(idx, c.MkInt(0)), c.MkLt(idx, c.MkLength(seq)))
	return o.finishIndex(inBounds, c.MkNth(seq, idx), guard, optional)
}

func (o *operatorTranslator) buildMapIndex(lhs, rhs, guard *smt.Term, optional bool) *smt.Term {
	ts := o.ts
	eks := ts.equalKeys(rhs)
	return o.finishIndex(ts.hasEqualKey(lhs, eks), ts.valueAtEqualKey(lhs, eks), guard, optional)
}

func (o *operatorTranslator) finishIndex(found, val, guard *smt.Term, optional bool) *smt.Term {
	c, ts := o.c, o.ts
	o.x.constrainValidValue(c.MkAnd(guard, found), val)
	if optional {
		ref := c.MkApp(ts.OptionalOfRefFunc(), val)
		o.x.addConstraint(c.MkEq(ts.GetOptionalValue(ref), val))
		o.x.addConstraint(ts.OptHasValue(ref))
		return c.MkITE(found, ts.MkOptionalOf(ref), ts.MkOptionalNone())
	}
	return c.MkITE(found, val, ts.MkError())
}

func (o *operatorTranslator) translateIndex(args []tv, a *ast.AST, optional bool) tv {
	c, ts := o.c, o.ts
	lhs, rhs := args[0], args[1]
	lhsType := exprType(a, lhs.expr)
	guaranteed := typeEquals(lhsType, o.guaranteedType(lhs))
	lz, rz := lhs.z3, rhs.z3
	isLhsOpt, lhsHasValue, shouldEval := c.MkFalse(), c.MkFalse(), c.MkTrue()
	if optional {
		isLhsOpt = ts.IsOptional(lz)
		ref := ts.GetOptionalRef(lz)
		lhsHasValue = ts.OptHasValue(ref)
		lz = c.MkITE(isLhsOpt, ts.GetOptionalValue(ref), lz)
		shouldEval = c.MkITE(isLhsOpt, lhsHasValue, c.MkTrue())
		if isOptionalType(lhsType) {
			lhsType = lhsType.Parameters()[0]
		}
	}
	elem := o.buildAndConstrainIndex(lz, rz, lhsType, guaranteed, shouldEval, optional)
	actual := elem.z3
	if optional {
		actual = c.MkITE(c.MkAnd(isLhsOpt, c.MkNot(lhsHasValue)), ts.MkOptionalNone(), actual)
	}
	opName := operators.Index
	if optional {
		opName = operators.OptIndex
	}
	listTrunc := o.x.recordUnrollLimitApproximation(c.MkAnd(
		shouldEval,
		ts.IsList(lz),
		ts.IsInt(rz),
		c.MkGe(ts.GetInt(rz), c.MkInt(int64(o.limit))),
		c.MkLt(ts.GetInt(rz), c.MkLength(ts.GetSeq(ts.GetListRef(lz))))))
	mapTrunc := c.MkAnd(shouldEval, o.x.isTruncatedMap(lz))
	return propagateStrictOp(ts, opName, actual, args...).
		withApproximation(c, MkOrFlattened(c, listTrunc, mapTrunc, elem.approx))
}

func (o *operatorTranslator) buildAndConstrainIndex(lz, rz *smt.Term, lhsType *types.Type, guaranteed bool, shouldEval *smt.Term, optional bool) tv {
	c, ts := o.c, o.ts
	var elemType *types.Type
	switch lhsType.Kind() {
	case types.ListKind:
		elemType = listElemType(lhsType)
	case types.MapKind:
		elemType = mapValueType(lhsType)
	}
	if elemType != nil {
		var actual *smt.Term
		if lhsType.Kind() == types.MapKind {
			actual = o.buildMapIndex(lz, rz, shouldEval, optional)
		} else {
			isIntIdx := ts.IsInt(rz)
			actual = c.MkITE(isIntIdx, o.buildListIndex(lz, rz, c.MkAnd(shouldEval, isIntIdx), optional), ts.MkError())
		}
		finalType := elemType
		if optional {
			finalType = types.NewOptionalType(elemType)
		}
		isDefined := c.MkAnd(shouldEval, c.MkNot(ts.IsError(actual)))
		tc := o.tcg.forType(actual, finalType)
		if guaranteed {
			o.x.addConstraint(c.MkImplies(isDefined, tc))
			return tv{actual, nil, c.MkFalse()}
		}
		return tv{actual, nil, MkAndFlattened(c, isDefined, MkNotFlattened(c, tc))}
	}
	isListGuard := c.MkAnd(shouldEval, ts.IsList(lz), ts.IsInt(rz))
	isMapGuard := c.MkAnd(shouldEval, ts.IsMap(lz))
	res := NewSwitch(c).
		Case(isListGuard, o.buildListIndex(lz, rz, isListGuard, optional)).
		Case(isMapGuard, o.buildMapIndex(lz, rz, isMapGuard, optional)).
		Build(ts.MkError())
	return tv{res, nil, c.MkFalse()}
}

func (o *operatorTranslator) translateConditional(args []tv, a *ast.AST) tv {
	c, ts := o.c, o.ts
	cond, t, f := args[0], args[1], args[2]
	condType := exprType(a, cond.expr)
	condTrue := c.MkAnd(ts.IsBool(cond.z3), ts.UnwrapBool(cond.z3))
	hasError := ts.IsError(cond.z3)
	hasUnknown := ts.IsUnknown(cond.z3)
	if !isExactly(condType, types.BoolType) {
		hasError = c.MkOr(hasError, c.MkNot(ts.IsBool(cond.z3)))
	}
	unknownResult := cond.z3
	if ts.isParameterizingUnknowns() {
		unknownResult = ts.mkParameterizedUnknown(operators.Conditional, []*smt.Term{cond.z3, t.z3, f.z3})
	}
	res := NewSwitch(c).
		Case(hasUnknown, unknownResult).
		Case(hasError, ts.MkError()).
		Case(condTrue, t.z3).
		Build(f.z3)
	safeError := c.MkAnd(hasError, c.MkNot(cond.approx))
	safeUnknown := c.MkAnd(hasUnknown, c.MkNot(cond.approx))
	taint := NewSwitch(c).
		Case(hasUnknown, c.MkNot(safeUnknown)).
		Case(hasError, c.MkNot(safeError)).
		Case(condTrue, c.MkOr(cond.approx, t.approx)).
		Build(c.MkOr(cond.approx, f.approx))
	return tv{res, nil, taint}
}

func (o *operatorTranslator) translateNotStrictlyFalse(args []tv) tv {
	c, ts := o.c, o.ts
	arg := args[0]
	isFalse := c.MkAnd(ts.IsBool(arg.z3), c.MkNot(ts.UnwrapBool(arg.z3)))
	return tv{ts.WrapBool(c.MkNot(isFalse)), nil, arg.approx}
}

// guaranteedType is the type v is guaranteed to conform to at runtime: the
// declared type of an input variable, or dyn.
func (o *operatorTranslator) guaranteedType(v tv) *types.Type { return o.x.guaranteedType(v.z3) }

// mayObserveTruncatedTypeConstraint is whether observing args together may
// expose a value beyond a truncated type constraint in any of them.
func (o *operatorTranslator) mayObserveTruncatedTypeConstraint(a *ast.AST, args ...tv) *smt.Term {
	c := o.c
	all := true
	for _, arg := range args {
		if !isConcrete(exprType(a, arg.expr)) {
			all = false
		}
	}
	if all {
		return c.MkFalse()
	}
	terms := make([]*smt.Term, len(args))
	for i, arg := range args {
		terms[i] = o.ts.hasTruncatedTypeConstraint(arg.z3)
	}
	return o.x.recordUnrollLimitApproximation(MkOrFlattened(c, terms...))
}
