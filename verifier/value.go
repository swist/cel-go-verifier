package verifier

import (
	"fmt"
	"strings"

	"cel.dev/cel-go/common/ast"
	"cel.dev/cel-go/common/types"
	"cel.dev/cel-go/common/types/ref"

	"github.com/swist/cel-go-verifier/smt"
)

// tv is a translated value: a CelValue term, the AST node it came from (if
// any), and the condition under which it may differ from the runtime value.
type tv struct {
	z3     *smt.Term
	expr   ast.Expr
	approx *smt.Term
}

func newTV(z3 *smt.Term, expr ast.Expr, approx *smt.Term) tv { return tv{z3, expr, approx} }

func (v tv) isLiteral(kind ast.ExprKind) bool { return v.expr != nil && v.expr.Kind() == kind }

func (v tv) listElementAt(i int) ast.Expr {
	if v.expr == nil || v.expr.Kind() != ast.ListKind {
		return nil
	}
	elems := v.expr.AsList().Elements()
	if i < len(elems) {
		return elems[i]
	}
	return nil
}

func (v tv) isNumericConstant() bool {
	if v.expr == nil || v.expr.Kind() != ast.LiteralKind {
		return false
	}
	switch v.expr.AsLiteral().Type() {
	case types.IntType, types.UintType, types.DoubleType:
		return true
	}
	return false
}

func (v tv) constant() ref.Val { return v.expr.AsLiteral() }

func (v tv) withApproximation(c *smt.Context, cond *smt.Term) tv {
	return tv{v.z3, v.expr, MkOrFlattened(c, v.approx, cond)}
}

// propagateStrict applies strict evaluation: an error or unknown argument
// short-circuits the result, and the result is approximate if an argument is,
// unless an exact error or unknown decides it.
func propagateStrict(ts *TypeSystem, opName string, base *smt.Term, expr ast.Expr, baseTaint *smt.Term, args []tv) tv {
	c := ts.c
	var exactErrors, exactUnknowns, unknowns []*smt.Term
	taints := []*smt.Term{baseTaint}
	var nonConst, all []*smt.Term
	for _, a := range args {
		all = append(all, a.z3)
		taints = append(taints, a.approx)
		if a.isLiteral(ast.LiteralKind) {
			continue
		}
		nonConst = append(nonConst, a.z3)
		isErr := ts.IsError(a.z3)
		isUnk := ts.IsUnknown(a.z3)
		isExact := MkNotFlattened(c, a.approx)
		unknowns = append(unknowns, isUnk)
		exactErrors = append(exactErrors, MkAndFlattened(c, isErr, isExact))
		exactUnknowns = append(exactUnknowns, MkAndFlattened(c, isUnk, isExact))
	}
	anyTaint := MkOrFlattened(c, taints...)
	if len(nonConst) == 0 {
		return tv{base, expr, anyTaint}
	}
	result := ts.propagateErrorAndUnknown(opName, base, nonConst, all)
	hasExactError := MkOrFlattened(c, exactErrors...)
	hasExactUnknown := MkOrFlattened(c, exactUnknowns...)
	hasUnknown := MkOrFlattened(c, unknowns...)
	isSafe := MkOrFlattened(c,
		hasExactUnknown,
		MkAndFlattened(c, hasExactError, MkNotFlattened(c, hasUnknown)),
		MkNotFlattened(c, anyTaint))
	return tv{result, expr, MkNotFlattened(c, isSafe)}
}

func propagateStrictOp(ts *TypeSystem, opName string, base *smt.Term, args ...tv) tv {
	return propagateStrict(ts, opName, base, nil, ts.c.MkFalse(), args)
}

func propagateStrictExpr(ts *TypeSystem, base *smt.Term, expr ast.Expr, args []tv) tv {
	return propagateStrict(ts, extractOpName(expr), base, expr, ts.c.MkFalse(), args)
}

// extractOpName names the operation performed by expr for parameterized unknowns.
func extractOpName(e ast.Expr) string {
	switch e.Kind() {
	case ast.SelectKind:
		s := e.AsSelect()
		return fmt.Sprintf("select_%s_%t", s.FieldName(), s.IsTestOnly())
	case ast.StructKind:
		s := e.AsStruct()
		var sb strings.Builder
		sb.WriteString("struct_" + s.TypeName())
		for _, f := range s.Fields() {
			fe := f.AsStructField()
			fmt.Fprintf(&sb, "_%s:%t", fe.Name(), fe.IsOptional())
		}
		return sb.String()
	case ast.MapKind:
		var sb strings.Builder
		sb.WriteString("MAP")
		for _, en := range e.AsMap().Entries() {
			fmt.Fprintf(&sb, "_%t", en.AsMapEntry().IsOptional())
		}
		return sb.String()
	case ast.ListKind:
		idx := e.AsList().OptionalIndices()
		parts := make([]string, len(idx))
		for i, x := range idx {
			parts[i] = fmt.Sprint(x)
		}
		return "LIST_[" + strings.Join(parts, ", ") + "]"
	}
	panic(fmt.Sprintf("verifier: unexpected expression kind %v", e.Kind()))
}
