package verifier

import (
	"bytes"
	"errors"
	"fmt"
	"math"
	"sort"

	"cel.dev/cel-go/cel"
	"cel.dev/cel-go/common"
	"cel.dev/cel-go/common/ast"
	"cel.dev/cel-go/common/operators"
	"cel.dev/cel-go/common/types"
	"cel.dev/cel-go/common/types/ref"

	exprpb "google.golang.org/genproto/googleapis/api/expr/v1alpha1"
)

// Canonicalization normalizes ASTs before equivalence checks, as cel-java's
// CanonicalizationOptimizer does: commutative && and || operands are sorted
// and deduplicated, == and != operands are ordered, and negations are pushed
// inward (De Morgan, including over all/exists).

const canonicalizationIterationLimit = 500

// cnode is a mutable copy of an expression.
type cnode struct {
	kind ast.ExprKind
	id   int64

	lit   ref.Val
	ident string

	operand  *cnode
	field    string
	testOnly bool

	fn     string
	target *cnode
	args   []*cnode

	elems  []*cnode
	optIdx []int32

	entries []*centry

	structName string
	fields     []*cfield

	comp *ccomp

	parent *cnode
}

type centry struct {
	key, value *cnode
	optional   bool
}

type cfield struct {
	name     string
	value    *cnode
	optional bool
}

type ccomp struct {
	iterVar, iterVar2, accuVar string
	iterRange, accuInit, cond, step, result *cnode
}

func fromAST(e ast.Expr) *cnode {
	n := &cnode{kind: e.Kind(), id: e.ID()}
	switch e.Kind() {
	case ast.LiteralKind:
		n.lit = e.AsLiteral()
	case ast.IdentKind:
		n.ident = e.AsIdent()
	case ast.SelectKind:
		s := e.AsSelect()
		n.operand, n.field, n.testOnly = fromAST(s.Operand()), s.FieldName(), s.IsTestOnly()
	case ast.CallKind:
		c := e.AsCall()
		n.fn = c.FunctionName()
		if c.IsMemberFunction() {
			n.target = fromAST(c.Target())
		}
		for _, a := range c.Args() {
			n.args = append(n.args, fromAST(a))
		}
	case ast.ListKind:
		l := e.AsList()
		for _, el := range l.Elements() {
			n.elems = append(n.elems, fromAST(el))
		}
		n.optIdx = append([]int32(nil), l.OptionalIndices()...)
	case ast.MapKind:
		for _, en := range e.AsMap().Entries() {
			me := en.AsMapEntry()
			n.entries = append(n.entries, &centry{fromAST(me.Key()), fromAST(me.Value()), me.IsOptional()})
		}
	case ast.StructKind:
		s := e.AsStruct()
		n.structName = s.TypeName()
		for _, f := range s.Fields() {
			fe := f.AsStructField()
			n.fields = append(n.fields, &cfield{fe.Name(), fromAST(fe.Value()), fe.IsOptional()})
		}
	case ast.ComprehensionKind:
		c := e.AsComprehension()
		n.comp = &ccomp{
			iterVar: c.IterVar(), iterVar2: c.IterVar2(), accuVar: c.AccuVar(),
			iterRange: fromAST(c.IterRange()), accuInit: fromAST(c.AccuInit()),
			cond: fromAST(c.LoopCondition()), step: fromAST(c.LoopStep()), result: fromAST(c.Result()),
		}
	}
	return n
}

func (n *cnode) children() []*cnode {
	switch n.kind {
	case ast.SelectKind:
		return []*cnode{n.operand}
	case ast.CallKind:
		var out []*cnode
		if n.target != nil {
			out = append(out, n.target)
		}
		return append(out, n.args...)
	case ast.ListKind:
		return n.elems
	case ast.MapKind:
		var out []*cnode
		for _, e := range n.entries {
			out = append(out, e.key, e.value)
		}
		return out
	case ast.StructKind:
		var out []*cnode
		for _, f := range n.fields {
			out = append(out, f.value)
		}
		return out
	case ast.ComprehensionKind:
		c := n.comp
		return []*cnode{c.iterRange, c.accuInit, c.cond, c.step, c.result}
	}
	return nil
}

func setParents(n *cnode, parent *cnode) {
	n.parent = parent
	for _, c := range n.children() {
		setParents(c, n)
	}
}

func postOrder(n *cnode, out *[]*cnode) {
	for _, c := range n.children() {
		postOrder(c, out)
	}
	*out = append(*out, n)
}

func (n *cnode) replaceChild(old, nw *cnode) {
	swap := func(p **cnode) bool {
		if *p == old {
			*p = nw
			return true
		}
		return false
	}
	switch n.kind {
	case ast.SelectKind:
		swap(&n.operand)
	case ast.CallKind:
		if n.target != nil && swap(&n.target) {
			return
		}
		for i := range n.args {
			if swap(&n.args[i]) {
				return
			}
		}
	case ast.ListKind:
		for i := range n.elems {
			if swap(&n.elems[i]) {
				return
			}
		}
	case ast.MapKind:
		for _, e := range n.entries {
			if swap(&e.key) || swap(&e.value) {
				return
			}
		}
	case ast.StructKind:
		for _, f := range n.fields {
			if swap(&f.value) {
				return
			}
		}
	case ast.ComprehensionKind:
		c := n.comp
		_ = swap(&c.iterRange) || swap(&c.accuInit) || swap(&c.cond) || swap(&c.step) || swap(&c.result)
	}
}

func call(fn string, args ...*cnode) *cnode { return &cnode{kind: ast.CallKind, fn: fn, args: args} }

func isCallN(n *cnode, fn string, argc int) bool {
	return n.kind == ast.CallKind && n.fn == fn && len(n.args) == argc
}

// macroCalls maps comprehension ids to the function name of the macro call that produced them.
type macroCalls map[int64]string

// canonicalizeExpr runs the canonicalization loop to a fixed point.
func canonicalizeExpr(root *cnode, macros macroCalls) (*cnode, error) {
	iter := 0
	for {
		if iter >= canonicalizationIterationLimit {
			return nil, errors.New("max iteration count reached in canonicalization")
		}
		iter++
		setParents(root, nil)
		var nodes []*cnode
		postOrder(root, &nodes)
		changed := false
		for _, cand := range nodes {
			if !canCanonicalize(cand) {
				continue
			}
			iter++
			if nw := maybeCanonicalize(cand, macros); nw != nil {
				if cand.parent == nil {
					root = nw
				} else {
					cand.parent.replaceChild(cand, nw)
				}
				changed = true
				break
			}
		}
		if !changed {
			return root, nil
		}
	}
}

func canCanonicalize(n *cnode) bool {
	return isCallN(n, operators.LogicalAnd, 2) || isCallN(n, operators.LogicalOr, 2) ||
		isCallN(n, operators.Equals, 2) || isCallN(n, operators.NotEquals, 2) ||
		isCallN(n, operators.LogicalNot, 1)
}

func maybeCanonicalize(n *cnode, macros macroCalls) *cnode {
	switch {
	case isCallN(n, operators.LogicalAnd, 2), isCallN(n, operators.LogicalOr, 2):
		return canonicalizeCommutative(n)
	case isCallN(n, operators.Equals, 2), isCallN(n, operators.NotEquals, 2):
		cmp := astComparator{scopeOf(n)}
		if cmp.compare(n.args[0], n.args[1]) > 0 {
			return call(n.fn, n.args[1], n.args[0])
		}
		return nil
	case isCallN(n, operators.LogicalNot, 1):
		return canonicalizeNot(n.args[0], macros)
	}
	return nil
}

func canonicalizeCommutative(n *cnode) *cnode {
	var ops []*cnode
	var flatten func(*cnode)
	flatten = func(e *cnode) {
		if isCallN(e, n.fn, 2) {
			flatten(e.args[0])
			flatten(e.args[1])
			return
		}
		ops = append(ops, e)
	}
	flatten(n)
	for _, op := range ops {
		if containsEnclosingAccuVar(op, n) {
			return nil
		}
	}
	cmp := astComparator{scopeOf(n)}
	sorted := append([]*cnode(nil), ops...)
	sort.SliceStable(sorted, func(i, j int) bool { return cmp.compare(sorted[i], sorted[j]) < 0 })
	var unique []*cnode
	for _, op := range sorted {
		if len(unique) == 0 || cmp.compare(op, unique[len(unique)-1]) != 0 {
			unique = append(unique, op)
		}
	}
	rebuilt := unique[0]
	for _, op := range unique[1:] {
		rebuilt = call(n.fn, rebuilt, op)
	}
	if cmp.compare(rebuilt, n) == 0 {
		return nil
	}
	return rebuilt
}

func negate(e *cnode) *cnode { return call(operators.LogicalNot, e) }

func canonicalizeNot(t *cnode, macros macroCalls) *cnode {
	switch {
	case isCallN(t, operators.LogicalNot, 1):
		return t.args[0]
	case isCallN(t, operators.LogicalAnd, 2):
		return call(operators.LogicalOr, negate(t.args[0]), negate(t.args[1]))
	case isCallN(t, operators.LogicalOr, 2):
		return call(operators.LogicalAnd, negate(t.args[0]), negate(t.args[1]))
	case isCallN(t, operators.Equals, 2):
		return call(operators.NotEquals, t.args[0], t.args[1])
	case isCallN(t, operators.NotEquals, 2):
		return call(operators.Equals, t.args[0], t.args[1])
	}
	return rewriteQuantifierDeMorgan(t, macros)
}

func rewriteQuantifierDeMorgan(t *cnode, macros macroCalls) *cnode {
	if t.kind != ast.ComprehensionKind {
		return nil
	}
	c := t.comp
	isStd := func(fn string) bool {
		m, ok := macros[t.id]
		return !ok || m == fn
	}
	boolInit := func(want bool) bool {
		if c.accuInit.kind != ast.LiteralKind {
			return false
		}
		b, ok := c.accuInit.lit.(types.Bool)
		return ok && bool(b) == want
	}
	nsf := func(expectNot bool) bool {
		cond := c.cond
		if cond.kind != ast.CallKind || (cond.fn != operators.NotStrictlyFalse && cond.fn != operators.OldNotStrictlyFalse) || len(cond.args) != 1 {
			return false
		}
		arg := cond.args[0]
		if expectNot {
			if !isCallN(arg, operators.LogicalNot, 1) {
				return false
			}
			arg = arg.args[0]
		}
		return arg.kind == ast.IdentKind && arg.ident == c.accuVar
	}
	stepWithAccu := func(fn string) bool {
		if !isCallN(c.step, fn, 2) {
			return false
		}
		isAccu := func(e *cnode) bool { return e.kind == ast.IdentKind && e.ident == c.accuVar }
		return isAccu(c.step.args[0]) || isAccu(c.step.args[1])
	}
	isExists := isStd(operators.Exists) && boolInit(false) && nsf(true) && stepWithAccu(operators.LogicalOr)
	isAll := !isExists && isStd(operators.All) && boolInit(true) && nsf(false) && stepWithAccu(operators.LogicalAnd)
	if !isExists && !isAll {
		return nil
	}
	pred := c.step.args[1]
	accu := func() *cnode { return &cnode{kind: ast.IdentKind, ident: c.accuVar} }
	stepFn, condArg := operators.LogicalOr, negate(accu())
	newMacro := operators.Exists
	if isExists {
		stepFn, condArg = operators.LogicalAnd, accu()
		newMacro = operators.All
	}
	if _, ok := macros[t.id]; ok {
		macros[t.id] = newMacro
	}
	return &cnode{kind: ast.ComprehensionKind, id: t.id, comp: &ccomp{
		iterVar: c.iterVar, iterVar2: c.iterVar2, accuVar: c.accuVar,
		iterRange: c.iterRange,
		accuInit:  &cnode{kind: ast.LiteralKind, lit: types.Bool(isExists)},
		cond:      call(operators.NotStrictlyFalse, condArg),
		step:      call(stepFn, accu(), negate(pred)),
		result:    c.result,
	}}
}

// cscope is a lexical scope chain of comprehension variables.
type cscope struct {
	name   string
	parent *cscope
}

func (s *cscope) push(name string) *cscope {
	if name == "" {
		return s
	}
	return &cscope{name, s}
}

func (s *cscope) forLoop(c *ccomp) *cscope   { return s.push(c.iterVar).push(c.iterVar2).push(c.accuVar) }
func (s *cscope) forResult(c *ccomp) *cscope { return s.push(c.accuVar) }

func (s *cscope) indexOf(name string) int {
	idx := 0
	for cur := s; cur != nil; cur = cur.parent {
		if cur.name == name {
			return idx
		}
		idx++
	}
	return -1
}

// scopeOf computes the scope at n from its ancestors.
func scopeOf(n *cnode) *cscope {
	if n.parent == nil {
		return nil
	}
	s := scopeOf(n.parent)
	if n.parent.kind == ast.ComprehensionKind {
		c := n.parent.comp
		switch n {
		case c.cond, c.step:
			return s.forLoop(c)
		case c.result:
			return s.forResult(c)
		}
	}
	return s
}

func containsEnclosingAccuVar(op, ctx *cnode) bool {
	var enclosing []*cnode
	for cur := ctx; cur.parent != nil; cur = cur.parent {
		p := cur.parent
		if p.kind == ast.ComprehensionKind && (cur == p.comp.cond || cur == p.comp.step) && p.comp.accuVar != "" {
			enclosing = append(enclosing, p)
		}
	}
	if len(enclosing) == 0 {
		return false
	}
	var nodes []*cnode
	postOrder(op, &nodes)
	for _, n := range nodes {
		if n.kind != ast.IdentKind {
			continue
		}
		decl := findDeclaringComprehension(n, n.ident)
		if decl == nil || decl.comp.accuVar != n.ident {
			continue
		}
		for _, e := range enclosing {
			if e == decl {
				return true
			}
		}
	}
	return false
}

func findDeclaringComprehension(n *cnode, name string) *cnode {
	if name == "" {
		return nil
	}
	for cur := n; cur.parent != nil; cur = cur.parent {
		p := cur.parent
		if p.kind != ast.ComprehensionKind {
			continue
		}
		c := p.comp
		if cur == c.iterRange || cur == c.accuInit {
			continue
		}
		if cur == c.result {
			if c.accuVar == name {
				return p
			}
			continue
		}
		if c.iterVar == name || c.iterVar2 == name || c.accuVar == name {
			return p
		}
	}
	return nil
}

// astComparator is a total order on expressions in a scope.
type astComparator struct{ scope *cscope }

func kindPriority(k ast.ExprKind) int {
	switch k {
	case ast.IdentKind:
		return 1
	case ast.SelectKind:
		return 2
	case ast.CallKind:
		return 3
	case ast.ListKind:
		return 4
	case ast.MapKind:
		return 5
	case ast.StructKind:
		return 6
	case ast.ComprehensionKind:
		return 7
	case ast.LiteralKind:
		return 8
	}
	return 99
}

func cmpInt(a, b int) int {
	switch {
	case a < b:
		return -1
	case a > b:
		return 1
	}
	return 0
}

func cmpStr(a, b string) int {
	switch {
	case a < b:
		return -1
	case a > b:
		return 1
	}
	return 0
}

func cmpBool(a, b bool) int {
	switch {
	case a == b:
		return 0
	case !a:
		return -1
	}
	return 1
}

func (c astComparator) compare(a, b *cnode) int {
	if r := cmpInt(kindPriority(a.kind), kindPriority(b.kind)); r != 0 {
		return r
	}
	switch a.kind {
	case ast.LiteralKind:
		return compareConstants(a.lit, b.lit)
	case ast.IdentKind:
		return compareIdent(a.ident, b.ident, c.scope)
	case ast.SelectKind:
		if r := c.compare(a.operand, b.operand); r != 0 {
			return r
		}
		if r := cmpStr(a.field, b.field); r != 0 {
			return r
		}
		return cmpBool(a.testOnly, b.testOnly)
	case ast.CallKind:
		if r := cmpStr(a.fn, b.fn); r != 0 {
			return r
		}
		if (a.target != nil) != (b.target != nil) {
			return cmpBool(a.target != nil, b.target != nil)
		}
		if a.target != nil {
			if r := c.compare(a.target, b.target); r != 0 {
				return r
			}
		}
		return c.compareList(a.args, b.args)
	case ast.ListKind:
		return c.compareList(a.elems, b.elems)
	case ast.MapKind:
		if r := cmpInt(len(a.entries), len(b.entries)); r != 0 {
			return r
		}
		for i := range a.entries {
			if r := c.compare(a.entries[i].key, b.entries[i].key); r != 0 {
				return r
			}
			if r := c.compare(a.entries[i].value, b.entries[i].value); r != 0 {
				return r
			}
		}
		return 0
	case ast.StructKind:
		if r := cmpStr(a.structName, b.structName); r != 0 {
			return r
		}
		if r := cmpInt(len(a.fields), len(b.fields)); r != 0 {
			return r
		}
		for i := range a.fields {
			if r := cmpStr(a.fields[i].name, b.fields[i].name); r != 0 {
				return r
			}
			if r := c.compare(a.fields[i].value, b.fields[i].value); r != 0 {
				return r
			}
		}
		return 0
	case ast.ComprehensionKind:
		x, y := a.comp, b.comp
		if r := c.compare(x.iterRange, y.iterRange); r != 0 {
			return r
		}
		if r := c.compare(x.accuInit, y.accuInit); r != 0 {
			return r
		}
		// compareTrueFirst, compareTrueFirst, compareFalseFirst.
		if r := -cmpBool(x.accuVar != "", y.accuVar != ""); r != 0 {
			return r
		}
		if r := -cmpBool(x.iterVar != "", y.iterVar != ""); r != 0 {
			return r
		}
		if r := cmpBool(x.iterVar2 != "", y.iterVar2 != ""); r != 0 {
			return r
		}
		loop := astComparator{c.scope.forLoop(x)}
		if r := loop.compare(x.cond, y.cond); r != 0 {
			return r
		}
		if r := loop.compare(x.step, y.step); r != 0 {
			return r
		}
		return astComparator{c.scope.forResult(x)}.compare(x.result, y.result)
	}
	return 0
}

func (c astComparator) compareList(a, b []*cnode) int {
	if r := cmpInt(len(a), len(b)); r != 0 {
		return r
	}
	for i := range a {
		if r := c.compare(a[i], b[i]); r != 0 {
			return r
		}
	}
	return 0
}

func compareIdent(a, b string, s *cscope) int {
	ia, ib := -1, -1
	if s != nil {
		ia, ib = s.indexOf(a), s.indexOf(b)
	}
	switch {
	case ia >= 0 && ib >= 0:
		return cmpInt(ib, ia)
	case ia >= 0:
		return -1
	case ib >= 0:
		return 1
	}
	return cmpStr(trimDot(a), trimDot(b))
}

func trimDot(s string) string {
	if len(s) > 0 && s[0] == '.' {
		return s[1:]
	}
	return s
}

func constantKindName(v ref.Val) string {
	switch v.(type) {
	case types.Null:
		return "NULL_VALUE"
	case types.Bool:
		return "BOOLEAN_VALUE"
	case types.Int:
		return "INT64_VALUE"
	case types.Uint:
		return "UINT64_VALUE"
	case types.Double:
		return "DOUBLE_VALUE"
	case types.String:
		return "STRING_VALUE"
	case types.Bytes:
		return "BYTES_VALUE"
	}
	return "NOT_SET"
}

func compareConstants(a, b ref.Val) int {
	if r := cmpStr(constantKindName(a), constantKindName(b)); r != 0 {
		return r
	}
	switch x := a.(type) {
	case types.Bool:
		return cmpBool(bool(x), bool(b.(types.Bool)))
	case types.Int:
		y := b.(types.Int)
		return cmpInt64(int64(x), int64(y))
	case types.Uint:
		y := b.(types.Uint)
		switch {
		case x < y:
			return -1
		case x > y:
			return 1
		}
		return 0
	case types.Double:
		return javaDoubleCompare(float64(x), float64(b.(types.Double)))
	case types.String:
		return cmpStr(string(x), string(b.(types.String)))
	case types.Bytes:
		return bytes.Compare(x, b.(types.Bytes))
	}
	return 0
}

func cmpInt64(a, b int64) int {
	switch {
	case a < b:
		return -1
	case a > b:
		return 1
	}
	return 0
}

// javaDoubleCompare is Double.compare: -0.0 < 0.0, and NaN is greater than everything.
func javaDoubleCompare(a, b float64) int {
	switch {
	case a < b:
		return -1
	case a > b:
		return 1
	}
	ab, bb := int64(math.Float64bits(a)), int64(math.Float64bits(b))
	if math.IsNaN(a) {
		ab = 0x7ff8000000000000
	}
	if math.IsNaN(b) {
		bb = 0x7ff8000000000000
	}
	return cmpInt64(ab, bb)
}

// toAST builds an expression with consecutive ids.
func toAST(n *cnode, f ast.ExprFactory, next *int64) ast.Expr {
	id := func() int64 { *next++; return *next }
	switch n.kind {
	case ast.LiteralKind:
		return f.NewLiteral(id(), n.lit)
	case ast.IdentKind:
		return f.NewIdent(id(), n.ident)
	case ast.SelectKind:
		i := id()
		op := toAST(n.operand, f, next)
		if n.testOnly {
			return f.NewPresenceTest(i, op, n.field)
		}
		return f.NewSelect(i, op, n.field)
	case ast.CallKind:
		i := id()
		var target ast.Expr
		if n.target != nil {
			target = toAST(n.target, f, next)
		}
		args := make([]ast.Expr, len(n.args))
		for j, a := range n.args {
			args[j] = toAST(a, f, next)
		}
		if target != nil {
			return f.NewMemberCall(i, n.fn, target, args...)
		}
		return f.NewCall(i, n.fn, args...)
	case ast.ListKind:
		i := id()
		elems := make([]ast.Expr, len(n.elems))
		for j, e := range n.elems {
			elems[j] = toAST(e, f, next)
		}
		return f.NewList(i, elems, n.optIdx)
	case ast.MapKind:
		i := id()
		entries := make([]ast.EntryExpr, len(n.entries))
		for j, e := range n.entries {
			ei := id()
			entries[j] = f.NewMapEntry(ei, toAST(e.key, f, next), toAST(e.value, f, next), e.optional)
		}
		return f.NewMap(i, entries)
	case ast.StructKind:
		i := id()
		fields := make([]ast.EntryExpr, len(n.fields))
		for j, fl := range n.fields {
			fi := id()
			fields[j] = f.NewStructField(fi, fl.name, toAST(fl.value, f, next), fl.optional)
		}
		return f.NewStruct(i, n.structName, fields)
	case ast.ComprehensionKind:
		i := id()
		c := n.comp
		return f.NewComprehensionTwoVar(i, toAST(c.iterRange, f, next), c.iterVar, c.iterVar2, c.accuVar,
			toAST(c.accuInit, f, next), toAST(c.cond, f, next), toAST(c.step, f, next), toAST(c.result, f, next))
	}
	panic(fmt.Sprintf("verifier: unexpected expression kind %v", n.kind))
}

// Canonicalize returns the canonical form of a checked AST, re-checked in env.
func Canonicalize(env *cel.Env, a *cel.Ast) (*cel.Ast, error) {
	native := a.NativeRep()
	macros := macroCalls{}
	for id, m := range native.SourceInfo().MacroCalls() {
		if m.Kind() == ast.CallKind {
			macros[id] = m.AsCall().FunctionName()
		}
	}
	root, err := canonicalizeExpr(fromAST(native.Expr()), macros)
	if err != nil {
		return nil, err
	}
	var next int64
	expr := toAST(root, ast.NewExprFactory(), &next)
	info := ast.NewSourceInfo(common.NewTextSource(a.Source().Content()))
	pe, err := ast.ToProto(ast.NewAST(expr, info))
	if err != nil {
		return nil, err
	}
	checked, iss := env.Check(cel.ParsedExprToAst(&exprpb.ParsedExpr{Expr: pe.GetExpr(), SourceInfo: pe.GetSourceInfo()}))
	if iss.Err() != nil {
		return nil, iss.Err()
	}
	return checked, nil
}

// canonicalizePair canonicalizes both ASTs before an equivalence check.
func (v *Verifier) canonicalizePair(a, b *cel.Ast) (*cel.Ast, *cel.Ast, error) {
	ca, err := Canonicalize(v.env, a)
	if err != nil {
		return nil, nil, err
	}
	cb, err := Canonicalize(v.env, b)
	if err != nil {
		return nil, nil, err
	}
	return ca, cb, nil
}
