package verifier

import (
	"sort"
	"strconv"
	"strings"

	"cel.dev/cel-go/common/ast"
	"cel.dev/cel-go/common/operators"
	"cel.dev/cel-go/common/types"
	"cel.dev/cel-go/common/types/ref"

	"github.com/swist/cel-go-verifier/smt"
)

// astTranslator translates checked CEL ASTs to Z3 terms over the CelValue
// datatype. One translator must translate every AST of a query, so that
// uninterpreted functions and constraints are shared.
type astTranslator struct {
	c             *smt.Context
	ts            *TypeSystem
	x             *translationContext
	tcg           *typeConstraintGenerator
	ops           *operatorTranslator
	comps         *comprehensionTranslator
	structs       *structTranslator
	unknownIdents map[string]bool
	listLiterals  map[*smt.Term]*smt.Term
}

func newASTTranslator(c *smt.Context, limit int, unknownIdents map[string]bool, r *functionRegistry, tp TypeProvider, parameterizeUnknowns bool) *astTranslator {
	ts := NewTypeSystem(c, parameterizeUnknowns)
	x := newTranslationContext(c, ts, limit)
	t := &astTranslator{c: c, ts: ts, x: x, tcg: x.tcg, unknownIdents: unknownIdents, listLiterals: map[*smt.Term]*smt.Term{}}
	t.ops = newOperatorTranslator(x, r)
	t.comps = &comprehensionTranslator{x: x, c: c, ts: ts, limit: limit, tr: t}
	t.structs = &structTranslator{x: x, c: c, ts: ts, tcg: x.tcg, tp: tp, tr: t, emptyMsg: map[string]*smt.Term{}}
	return t
}

func (t *astTranslator) isTrue(v *smt.Term) *smt.Term {
	return t.c.MkAnd(t.ts.IsBool(v), t.ts.UnwrapBool(v))
}

func (t *astTranslator) bindSymbol(name string, v tv) { t.x.bindSymbol(name, v) }

func (t *astTranslator) translate(a *ast.AST) tv {
	var res tv
	if idx, result, ok := extractBlock(a.Expr()); ok {
		res = t.translateBlock(idx, 0, result, a)
	} else {
		res = t.translateExpr(a.Expr(), a)
	}
	visited := map[*smt.Term]bool{}
	var listRefs, mapRefs, msgRefs, optRefs []*smt.Term
	var collect func(*smt.Term)
	collect = func(e *smt.Term) {
		if visited[e] {
			return
		}
		visited[e] = true
		switch e.Sort {
		case t.ts.listRefSort:
			listRefs = append(listRefs, e)
		case t.ts.mapRefSort:
			mapRefs = append(mapRefs, e)
		case t.ts.messageRefSort:
			msgRefs = append(msgRefs, e)
		}
		if e.IsApp() && t.ts.isOptionalRefAccessor(e) {
			optRefs = append(optRefs, e)
		}
		if e.IsApp() {
			for _, arg := range e.Args {
				collect(arg)
			}
		}
	}
	for _, k := range append([]*smt.Term(nil), t.x.constraints...) {
		collect(k)
	}
	collect(res.z3)
	for _, ax := range extensionalityAxioms(t.ts, listRefs, mapRefs, msgRefs) {
		t.x.addConstraint(ax)
	}
	for _, r := range optRefs {
		t.x.constrainValidValue(t.c.MkAnd(t.ts.IsOptional(r.Args[0]), t.ts.OptHasValue(r)), t.ts.GetOptionalValue(r))
	}
	return res
}

const blockIndexPrefix = "@index"

// extractBlock recognizes cel.@block([e0, e1, ...], result).
func extractBlock(e ast.Expr) ([]ast.Expr, ast.Expr, bool) {
	if e.Kind() != ast.CallKind || e.AsCall().FunctionName() != "cel.@block" {
		return nil, nil, false
	}
	args := e.AsCall().Args()
	if len(args) != 2 || args[0].Kind() != ast.ListKind {
		return nil, nil, false
	}
	return args[0].AsList().Elements(), args[1], true
}

func (t *astTranslator) translateBlock(bound []ast.Expr, i int, result ast.Expr, a *ast.AST) tv {
	if i >= len(bound) {
		return t.translateExpr(result, a)
	}
	sub := t.translateExpr(bound[i], a)
	return withScope(t.x, blockIndexPrefix+strconv.Itoa(i), sub, func() tv {
		return t.translateBlock(bound, i+1, result, a)
	})
}

func (t *astTranslator) translateExpr(e ast.Expr, a *ast.AST) tv {
	switch e.Kind() {
	case ast.LiteralKind:
		return t.translateConstant(e, e.AsLiteral())
	case ast.IdentKind:
		return t.translateIdent(e, a)
	case ast.SelectKind:
		if name, ok := qualifiedIdent(a, e); ok {
			return t.translateNamedIdent(e, name, a)
		}
		return t.structs.translateSelect(e, a)
	case ast.CallKind:
		return t.translateCall(e, a)
	case ast.ListKind:
		return t.translateList(e, a)
	case ast.MapKind:
		return t.translateMap(e, a)
	case ast.StructKind:
		return t.structs.translateStruct(e, a)
	case ast.ComprehensionKind:
		return t.comps.translate(e, a)
	}
	panic("verifier: unsupported expression kind")
}

func (t *astTranslator) translateConstant(e ast.Expr, v ref.Val) tv {
	ts := t.ts
	var z *smt.Term
	switch val := v.(type) {
	case types.Bool:
		z = ts.MkBool(bool(val))
	case types.Int:
		z = ts.MkInt(int64(val))
	case types.Uint:
		z = ts.MkUint64(uint64(val))
	case types.Double:
		z = ts.MkDouble(float64(val))
	case types.String:
		z = ts.MkString(string(val))
	case types.Bytes:
		z = ts.MkBytes(string(val))
	case types.Null:
		z = ts.MkNull()
	default:
		panic("verifier: unsupported constant " + v.Type().TypeName())
	}
	return tv{z, e, t.c.MkFalse()}
}

func (t *astTranslator) translateIdent(e ast.Expr, a *ast.AST) tv {
	if v := referenceValue(a, e); v != nil {
		return t.translateConstant(ast.NewExprFactory().NewLiteral(e.ID(), v), v)
	}
	return t.translateNamedIdent(e, identName(a, e), a)
}

func (t *astTranslator) translateNamedIdent(e ast.Expr, name string, a *ast.AST) tv {
	c, ts := t.c, t.ts
	typ := exprType(a, e)
	if typ.Kind() == types.TypeKind && len(typ.Parameters()) > 0 && typ.Parameters()[0].Kind() != types.DynKind {
		return tv{ts.MkString(typ.Parameters()[0].TypeName()), e, c.MkFalse()}
	}
	v := t.x.computeSymbolIfAbsent(name, func(n string) tv {
		z := c.MkConst(n, ts.celValueSort)
		t.x.addInputVariable(z, typ)
		// Variables at rest are never errors.
		t.x.addConstraint(c.MkNot(ts.IsError(z)))
		tc := t.tcg.createTypeConstraint(z, e, a)
		if t.unknownIdents[n] {
			t.x.addConstraint(c.MkOr(ts.IsUnknown(z), tc))
		} else {
			t.x.addConstraint(c.MkNot(ts.IsUnknown(z)))
			t.x.addConstraint(tc)
		}
		return tv{z, e, c.MkFalse()}
	})
	return tv{v.z3, e, v.approx}
}

func (t *astTranslator) translateList(e ast.Expr, a *ast.AST) tv {
	c, ts := t.c, t.ts
	l := e.AsList()
	var elems []tv
	seq := c.MkEmptySeq(c.SeqSort(ts.celValueSort))
	var values []*smt.Term
	for i, el := range l.Elements() {
		v := t.translateExpr(el, a)
		if l.IsOptional(int32(i)) {
			checked := ts.WithRuntimeError(v.z3, c.MkNot(ts.IsOptional(v.z3)))
			v = tv{checked, el, v.approx}
			ref := ts.GetOptionalRef(v.z3)
			value := ts.GetOptionalValue(ref)
			seq = c.MkITE(ts.OptHasValue(ref), ts.MkConcatSafe(seq, c.MkUnit(value)), seq)
			values = append(values, value)
		} else {
			seq = ts.MkConcatSafe(seq, c.MkUnit(v.z3))
			values = append(values, v.z3)
		}
		elems = append(elems, v)
	}
	ref, ok := t.listLiterals[seq]
	if !ok {
		ref = ts.MkListRefConst("!listRef_")
		t.x.addConstraint(c.MkEq(ts.GetSeq(ref), seq))
		t.propagateTruncatedTypeConstraint(ts.WrapList(ref), values)
		t.listLiterals[seq] = ref
	}
	return propagateStrictExpr(ts, ts.WrapList(ref), e, elems)
}

func (t *astTranslator) translateMap(e ast.Expr, a *ast.AST) tv {
	c, ts := t.c, t.ts
	m := e.AsMap()
	ref := ts.MkMapRefConst("!mapRef_")
	values := c.MkConstArray(ts.celValueSort, ts.MkUnknown())
	presence := c.MkConstArray(ts.celValueSort, c.MkFalse())
	keys := c.MkEmptySeq(c.SeqSort(ts.celValueSort))
	var elems []tv
	var vals []*smt.Term
	var invalid []*smt.Term
	var soFarKeys []*smt.Term
	soFar := map[*smt.Term]*smt.Term{}
	for _, en := range m.Entries() {
		me := en.AsMapEntry()
		kv := t.translateExpr(me.Key(), a)
		key := kv.z3
		elems = append(elems, kv)
		invalid = append(invalid, c.MkNot(c.MkOr(ts.IsString(key), ts.IsInt(key), ts.IsUint(key), ts.IsBool(key))))
		for _, ek := range ts.equalKeys(key) {
			for _, earlier := range soFarKeys {
				repeats := c.MkAnd(soFar[earlier], ek.Cond, c.MkEq(earlier, ek.Key))
				if !c.Simplify(repeats).IsFalse() {
					invalid = append(invalid, repeats)
				}
			}
		}
		vv := t.translateExpr(me.Value(), a)
		value := vv.z3
		final := value
		finalPresence := c.MkTrue()
		if me.IsOptional() {
			checked := ts.WithRuntimeError(value, c.MkNot(ts.IsOptional(value)))
			vv = tv{checked, me.Value(), vv.approx}
			oref := ts.GetOptionalRef(checked)
			finalPresence = ts.OptHasValue(oref)
			final = ts.GetOptionalValue(oref)
		}
		elems = append(elems, vv)
		vals = append(vals, final)
		if prev, ok := soFar[key]; ok {
			soFar[key] = c.MkOr(prev, finalPresence)
		} else {
			soFar[key] = finalPresence
			soFarKeys = append(soFarKeys, key)
		}
		alreadyPresent := c.MkSelect(presence, key)
		shouldInsert := c.MkAnd(c.MkNot(alreadyPresent), finalPresence)
		keys = c.MkITE(shouldInsert, ts.MkConcatSafe(keys, c.MkUnit(key)), keys)
		values = c.MkITE(finalPresence, c.MkStore(values, key, final), values)
		presence = c.MkITE(finalPresence, c.MkStore(presence, key, c.MkTrue()), presence)
	}
	t.x.addConstraint(c.MkEq(ts.GetMapValues(ref), values))
	t.x.addConstraint(c.MkEq(ts.GetMapPresence(ref), presence))
	t.x.addConstraint(c.MkEq(ts.GetMapKeys(ref), keys))
	res := ts.WithRuntimeError(ts.WrapMap(ref), MkOrFlattened(c, invalid...))
	t.propagateTruncatedTypeConstraint(res, vals)
	return propagateStrictExpr(ts, res, e, elems)
}

// propagateTruncatedTypeConstraint marks container as having a truncated type
// constraint if any of elements has one, unless it's an error or unknown.
func (t *astTranslator) propagateTruncatedTypeConstraint(container *smt.Term, elements []*smt.Term) {
	c, ts := t.c, t.ts
	has := c.MkOr(ts.IsErrorOrUnknown(container), ts.hasTruncatedTypeConstraint(container))
	for _, el := range elements {
		t.x.addConstraint(c.MkImplies(ts.hasTruncatedTypeConstraint(el), has))
	}
}

func (t *astTranslator) translateCall(e ast.Expr, a *ast.AST) tv {
	c, ts := t.c, t.ts
	call := e.AsCall()
	fn := call.FunctionName()
	var args []tv
	if call.IsMemberFunction() {
		args = append(args, t.translateExpr(call.Target(), a))
	}
	for _, arg := range call.Args() {
		args = append(args, t.translateExpr(arg, a))
	}
	if res, ok := t.ops.translateFunctionCall(fn, args, e, a); ok {
		if mayEmbedArgs(fn, exprType(a, e)) {
			zs := make([]*smt.Term, len(args))
			for i, arg := range args {
				zs[i] = arg.z3
			}
			t.propagateTruncatedTypeConstraint(res.z3, zs)
		}
		return tv{res.z3, e, res.approx}
	}
	// Uninterpreted function.
	sorts := make([]*smt.Sort, len(args))
	zs := make([]*smt.Term, len(args))
	for i, arg := range args {
		sorts[i] = ts.celValueSort
		zs[i] = arg.z3
	}
	f := ts.InternFuncDecl(uninterpretedFunctionSymbol(e, a), sorts, ts.celValueSort)
	res := c.MkApp(f, zs...)
	t.x.addConstraint(t.tcg.createTypeConstraint(res, e, a))
	t.x.addConstraint(c.MkNot(ts.IsUnknown(res)))
	t.x.addConstraint(c.MkNot(ts.IsError(res)))
	// The solver picks the result freely, so a model depending on it is never exact.
	return propagateStrict(ts, fn, res, e, t.x.recordCallApproximation(fn, c.MkTrue()), args)
}

// uninterpretedFunctionSymbol names an uninterpreted call by its sorted candidate overloads.
func uninterpretedFunctionSymbol(e ast.Expr, a *ast.AST) string {
	var ids []string
	if r, ok := a.ReferenceMap()[e.ID()]; ok && r != nil {
		ids = append(ids, r.OverloadIDs...)
	}
	sort.Strings(ids)
	ids = dedupe(ids)
	return "!fn_" + strings.Join(ids, "|")
}

func dedupe(s []string) []string {
	var out []string
	for i, x := range s {
		if i == 0 || x != s[i-1] {
			out = append(out, x)
		}
	}
	return out
}

// mayEmbedArgs reports whether a call may build a container embedding its args.
func mayEmbedArgs(fn string, result *types.Type) bool {
	return (!isStaticallyKnown(result) || len(result.Parameters()) > 0) &&
		fn != operators.Index && fn != operators.Conditional
}
