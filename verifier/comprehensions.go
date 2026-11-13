package verifier

import (
	"strconv"

	"cel.dev/cel-go/common/ast"
	"cel.dev/cel-go/common/operators"
	"cel.dev/cel-go/common/types"

	"github.com/swist/cel-go-verifier/smt"
)

// comprehensionTranslator unrolls comprehensions up to the unroll limit.
type comprehensionTranslator struct {
	x     *translationContext
	c     *smt.Context
	ts    *TypeSystem
	limit int
	tr    *astTranslator
}

type iterationElement struct{ keyOrIndex, value *smt.Term }

func (ct *comprehensionTranslator) translate(e ast.Expr, a *ast.AST) tv {
	c, ts := ct.c, ct.ts
	comp := e.AsComprehension()
	rangeExpr := comp.IterRange()
	if rangeExpr.Kind() == ast.IdentKind {
		if v, ok := ct.x.lookupSymbol(rangeExpr.AsIdent()); ok && v.expr != nil {
			rangeExpr = v.expr
		}
	}
	var elems []iterationElement
	var taints []*smt.Term
	var allRange []*smt.Term
	switch {
	case rangeExpr.Kind() == ast.ListKind && len(rangeExpr.AsList().OptionalIndices()) == 0:
		for i, el := range rangeExpr.AsList().Elements() {
			v := ct.tr.translateExpr(el, a)
			taints = append(taints, v.approx)
			elems = append(elems, iterationElement{ts.MkInt(int64(i)), v.z3})
			allRange = append(allRange, v.z3)
		}
	case rangeExpr.Kind() == ast.MapKind && !hasOptionalEntry(rangeExpr):
		for _, en := range rangeExpr.AsMap().Entries() {
			me := en.AsMapEntry()
			k := ct.tr.translateExpr(me.Key(), a)
			taints = append(taints, k.approx)
			v := ct.tr.translateExpr(me.Value(), a)
			taints = append(taints, v.approx)
			elems = append(elems, iterationElement{k.z3, v.z3})
			allRange = append(allRange, k.z3, v.z3)
		}
	default:
		return ct.translateDynamic(e, a)
	}
	accuTV := ct.tr.translateExpr(comp.AccuInit(), a)
	accu := accuTV.z3
	taints = append(taints, accuTV.approx)
	isMap := rangeExpr.Kind() == ast.MapKind
	isTwoVar := comp.IterVar2() != ""
	for _, el := range elems {
		cur := accu
		accu = withIterationScope(ct, comp, el.keyOrIndex, el.value, cur, isMap, isTwoVar, func() *smt.Term {
			cond := ct.tr.translateExpr(comp.LoopCondition(), a)
			step := ct.tr.translateExpr(comp.LoopStep(), a)
			taints = append(taints, step.approx)
			return c.MkITE(ts.UnwrapBool(cond.z3), step.z3, cur)
		})
	}
	res := withScope(ct.x, comp.AccuVar(), tv{accu, nil, MkOrFlattened(c, taints...)}, func() tv {
		return ct.tr.translateExpr(comp.Result(), a)
	})
	return tv{
		ts.propagateErrorAndUnknown("comprehension", res.z3, allRange, append([]*smt.Term{res.z3}, allRange...)),
		e, res.approx,
	}
}

func hasOptionalEntry(e ast.Expr) bool {
	for _, en := range e.AsMap().Entries() {
		if en.AsMapEntry().IsOptional() {
			return true
		}
	}
	return false
}

func (ct *comprehensionTranslator) translateDynamic(e ast.Expr, a *ast.AST) tv {
	c, ts := ct.c, ct.ts
	comp := e.AsComprehension()
	rangeTV := ct.tr.translateExpr(comp.IterRange(), a)
	rng := rangeTV.z3
	rangeType := exprType(a, comp.IterRange())
	isList := rangeType.Kind() == types.ListKind
	isMap := rangeType.Kind() == types.MapKind
	if !isList && !isMap {
		isRuntimeListOrMap := ct.x.recordApproximation("comprehensions over `dyn` values",
			c.MkOr(ts.IsList(rng), ts.IsMap(rng)))
		ct.x.addUnmodeledResult(isRuntimeListOrMap)
		res := c.MkITE(c.MkOr(ts.IsUnknown(rangeTV.z3), isRuntimeListOrMap), ct.mkParameterizedUnknown(e, a), ts.MkError())
		return tv{res, e, MkOrFlattened(c, rangeTV.approx, isRuntimeListOrMap)}
	}
	var seq, presence *smt.Term
	if isMap {
		seq = ts.GetMapKeys(ts.GetMapRef(rng))
		presence = ts.GetMapPresence(ts.GetMapRef(rng))
	} else {
		seq = ts.GetSeq(ts.GetListRef(rng))
	}
	length := c.MkLength(seq)
	validRange := ts.IsList(rng)
	if isMap {
		validRange = ts.IsMap(rng)
	}
	isTruncated := ct.x.recordUnrollLimitApproximation(c.MkAnd(validRange, c.MkGt(length, c.MkInt(int64(ct.limit)))))
	ct.x.addUnmodeledResult(isTruncated)
	if isAllMacro(comp) || isExistsMacro(comp) {
		return ct.unrollAllAndExists(e, a, seq, length, presence, isTruncated, rangeTV)
	}
	return ct.unrollMapAndFilter(e, a, seq, length, presence, isTruncated, rangeTV)
}

func withIterationScope[T any](ct *comprehensionTranslator, comp ast.ComprehensionExpr, keyOrIndex, value, accu *smt.Term, isMap, isTwoVar bool, f func() T) T {
	c := ct.c
	bindAccu := func() T {
		return withScope(ct.x, comp.AccuVar(), tv{accu, nil, c.MkFalse()}, f)
	}
	if isTwoVar {
		return withScope(ct.x, comp.IterVar(), tv{keyOrIndex, nil, c.MkFalse()}, func() T {
			return withScope(ct.x, comp.IterVar2(), tv{value, nil, c.MkFalse()}, bindAccu)
		})
	}
	iterVal := value
	if isMap {
		iterVal = keyOrIndex
	}
	return withScope(ct.x, comp.IterVar(), tv{iterVal, nil, c.MkFalse()}, bindAccu)
}

func (ct *comprehensionTranslator) iterationElement(x, idx, rng *smt.Term, isMap, isTwoVar bool) iterationElement {
	ts := ct.ts
	if isMap {
		if isTwoVar {
			return iterationElement{x, ct.c.MkSelect(ts.GetMapValues(ts.GetMapRef(rng)), x)}
		}
		return iterationElement{x, nil}
	}
	if isTwoVar {
		return iterationElement{ts.WrapInt(idx), x}
	}
	return iterationElement{nil, x}
}

type boundedIteration struct {
	inBounds *smt.Term
	step     tv
}

func (ct *comprehensionTranslator) unrollAllAndExists(e ast.Expr, a *ast.AST, seq, length, presence, isTruncated *smt.Term, rangeTV tv) tv {
	c := ct.c
	comp := e.AsComprehension()
	var iters []boundedIteration
	accuInit := ct.tr.translateExpr(comp.AccuInit(), a)
	isMap := presence != nil
	isTwoVar := comp.IterVar2() != ""
	for i := 0; i < ct.limit; i++ {
		idx := c.MkInt(int64(i))
		inBounds := c.MkLt(idx, length)
		x := c.MkNth(seq, idx)
		ct.constrainIterationElement(idx, length, x, inBounds, presence, rangeTV.z3)
		el := ct.iterationElement(x, idx, rangeTV.z3, isMap, isTwoVar)
		step := withIterationScope(ct, comp, el.keyOrIndex, el.value, accuInit.z3, isMap, isTwoVar, func() tv {
			return ct.tr.translateExpr(comp.LoopStep(), a)
		})
		iters = append(iters, boundedIteration{inBounds, step})
	}
	return ct.reduceAllOrExists(iters, isTruncated, rangeTV, isAllMacro(comp), e, a)
}

func (ct *comprehensionTranslator) unrollMapAndFilter(e ast.Expr, a *ast.AST, seq, length, presence, isTruncated *smt.Term, rangeTV tv) tv {
	c, ts := ct.c, ct.ts
	comp := e.AsComprehension()
	accuTV := ct.tr.translateExpr(comp.AccuInit(), a)
	accu := accuTV.z3
	isMap := presence != nil
	isTwoVar := comp.IterVar2() != ""
	taints := []*smt.Term{accuTV.approx, rangeTV.approx}
	for i := 0; i < ct.limit; i++ {
		idx := c.MkInt(int64(i))
		inBounds := c.MkLt(idx, length)
		x := c.MkNth(seq, idx)
		ct.constrainIterationElement(idx, length, x, inBounds, presence, rangeTV.z3)
		cur := accu
		el := ct.iterationElement(x, idx, rangeTV.z3, isMap, isTwoVar)
		step := withIterationScope(ct, comp, el.keyOrIndex, el.value, cur, isMap, isTwoVar, func() tv {
			return ct.tr.translateExpr(comp.LoopStep(), a)
		})
		taints = append(taints, c.MkAnd(inBounds, step.approx))
		accu = c.MkITE(inBounds, step.z3, cur)
	}
	res := withScope(ct.x, comp.AccuVar(), tv{accu, nil, MkOrFlattened(c, taints...)}, func() tv {
		return ct.tr.translateExpr(comp.Result(), a)
	})
	rangeIsError := ts.IsError(rangeTV.z3)
	rangeIsUnknown := ts.IsUnknown(rangeTV.z3)
	conditionUnmodeled := c.MkFalse()
	if !isLiteralTrue(comp.LoopCondition()) {
		conditionUnmodeled = ct.x.recordApproximation("comprehensions with a loop condition", c.MkTrue())
		ct.x.addUnmodeledResult(conditionUnmodeled)
	}
	isAbstracted := MkOrFlattened(c, rangeIsUnknown, isTruncated, conditionUnmodeled)
	final := NewSwitch(c).
		Case(rangeIsError, ts.MkError()).
		Case(isAbstracted, ct.mkParameterizedUnknown(e, a)).
		Build(res.z3)
	taint := c.MkITE(c.MkOr(rangeIsError, rangeIsUnknown), rangeTV.approx,
		MkOrFlattened(c, res.approx, isTruncated, conditionUnmodeled))
	return tv{final, e, taint}
}

func (ct *comprehensionTranslator) constrainIterationElement(idx, length, x, inBounds, presence, rng *smt.Term) {
	c, ts := ct.c, ct.ts
	ct.x.addConstraint(c.MkImplies(c.MkGe(idx, length), c.MkEq(x, ts.MkUnknown())))
	if presence != nil {
		ct.x.addConstraint(c.MkImplies(inBounds, c.MkSelect(presence, x)))
	}
	if !hasConcreteElements(ct.x.guaranteedType(rng)) {
		kind := ts.IsList(rng)
		if presence != nil {
			kind = ts.IsMap(rng)
		}
		ct.x.constrainValidValue(c.MkAnd(kind, inBounds), x)
	}
}

func (ct *comprehensionTranslator) reduceAllOrExists(iters []boundedIteration, isTruncated *smt.Term, rangeTV tv, isAll bool, e ast.Expr, a *ast.AST) tv {
	c, ts := ct.c, ct.ts
	var hasMatchL, hasErrorL, hasUnknownL, hasSafeMatchL, activeTaints []*smt.Term
	for _, it := range iters {
		step := it.step.z3
		isBool := ts.IsBool(step)
		unwrap := ts.UnwrapBool(step)
		matchCond := unwrap
		if isAll {
			matchCond = c.MkNot(unwrap)
		}
		isMatch := c.MkAnd(isBool, matchCond)
		isU := ts.IsUnknown(step)
		isE := c.MkOr(ts.IsError(step), c.MkAnd(c.MkNot(isBool), c.MkNot(isU)))
		active := it.inBounds
		hasMatchL = append(hasMatchL, MkAndFlattened(c, active, isMatch))
		hasErrorL = append(hasErrorL, MkAndFlattened(c, active, isE))
		hasUnknownL = append(hasUnknownL, MkAndFlattened(c, active, isU))
		hasSafeMatchL = append(hasSafeMatchL, MkAndFlattened(c, active, isMatch, MkNotFlattened(c, it.step.approx)))
		activeTaints = append(activeTaints, MkAndFlattened(c, active, it.step.approx))
	}
	hasMatch := MkOrFlattened(c, hasMatchL...)
	hasError := MkOrFlattened(c, hasErrorL...)
	hasUnknown := MkOrFlattened(c, hasUnknownL...)
	rangeIsError := ts.IsError(rangeTV.z3)
	rangeIsUnknown := ts.IsUnknown(rangeTV.z3)
	hasSafeMatch := MkOrFlattened(c, hasSafeMatchL...)
	anyActiveTaint := MkOrFlattened(c, activeTaints...)
	unknown := ct.mkParameterizedUnknown(e, a)
	res := NewSwitch(c).
		Case(rangeIsError, ts.MkError()).
		Case(rangeIsUnknown, unknown).
		Case(hasMatch, ts.MkBool(!isAll)).
		Case(c.MkOr(hasUnknown, isTruncated), unknown).
		Case(hasError, ts.MkError()).
		Build(ts.MkBool(isAll))
	taint := NewSwitch(c).
		Case(c.MkOr(rangeIsError, rangeIsUnknown), rangeTV.approx).
		Case(hasMatch, c.MkOr(rangeTV.approx, c.MkNot(hasSafeMatch))).
		Case(c.MkOr(hasUnknown, isTruncated), c.MkOr(rangeTV.approx, isTruncated, anyActiveTaint)).
		Case(hasError, c.MkOr(rangeTV.approx, anyActiveTaint)).
		Build(MkOrFlattened(c, anyActiveTaint, rangeTV.approx))
	return tv{res, e, taint}
}

func isAllMacro(comp ast.ComprehensionExpr) bool {
	return isBooleanAccuInit(comp, true) && isNotStrictlyFalseLoopCondition(comp, false)
}

func isExistsMacro(comp ast.ComprehensionExpr) bool {
	return isBooleanAccuInit(comp, false) && isNotStrictlyFalseLoopCondition(comp, true)
}

func isBooleanAccuInit(comp ast.ComprehensionExpr, want bool) bool {
	init := comp.AccuInit()
	if init.Kind() != ast.LiteralKind {
		return false
	}
	b, ok := init.AsLiteral().(types.Bool)
	return ok && bool(b) == want
}

func isLiteralTrue(e ast.Expr) bool {
	if e.Kind() != ast.LiteralKind {
		return false
	}
	b, ok := e.AsLiteral().(types.Bool)
	return ok && bool(b)
}

func isNotStrictlyFalseLoopCondition(comp ast.ComprehensionExpr, expectNot bool) bool {
	cond := comp.LoopCondition()
	if cond.Kind() != ast.CallKind {
		return false
	}
	call := cond.AsCall()
	if call.FunctionName() != operators.NotStrictlyFalse && call.FunctionName() != operators.OldNotStrictlyFalse {
		return false
	}
	arg := call.Args()[0]
	if expectNot {
		if arg.Kind() != ast.CallKind || arg.AsCall().FunctionName() != operators.LogicalNot {
			return false
		}
		arg = arg.AsCall().Args()[0]
	}
	return arg.Kind() == ast.IdentKind && arg.AsIdent() == comp.AccuVar()
}

func (ct *comprehensionTranslator) mkParameterizedUnknown(e ast.Expr, a *ast.AST) *smt.Term {
	sig := computeAlphaSignature(e, a)
	var args []*smt.Term
	for _, fv := range sig.freeVars {
		args = append(args, ct.tr.translateExpr(fv, a).z3)
	}
	return ct.ts.mkParameterizedUnknown("!trunc_"+strconv.FormatUint(sig.staticHash, 16), args)
}
