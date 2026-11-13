package verifier

import (
	"cel.dev/cel-go/common/ast"
	"cel.dev/cel-go/common/types"

	"github.com/swist/cel-go-verifier/smt"
)

// typeConstraintGenerator restricts terms to the values of CEL types.
type typeConstraintGenerator struct {
	c           *smt.Context
	ts          *TypeSystem
	unrollLimit int
}

func (g *typeConstraintGenerator) createTypeConstraint(v *smt.Term, e ast.Expr, a *ast.AST) *smt.Term {
	return g.c.MkOr(g.ts.IsErrorOrUnknown(v), g.forType(v, exprType(a, e)))
}

// forType returns whether v is a value of type t. Containers are constrained
// up to the unroll limit rather than with quantifiers.
func (g *typeConstraintGenerator) forType(v *smt.Term, t *types.Type) *smt.Term {
	c, ts := g.c, g.ts
	if isNullable(t) {
		return c.MkOr(ts.IsNull(v), g.forType(v, nullableTarget(t)))
	}
	if isOptionalType(t) {
		isOpt := ts.IsOptional(v)
		param := t.Parameters()[0]
		ref := ts.GetOptionalRef(v)
		hasValue := ts.OptHasValue(ref)
		optVal := ts.GetOptionalValue(ref)
		valConstraint := c.MkAnd(c.MkNot(ts.IsErrorOrUnknown(optVal)), g.forType(optVal, param))
		return c.MkAnd(isOpt, c.MkImplies(hasValue, valConstraint))
	}
	switch {
	case isExactly(t, types.BoolType):
		return ts.IsBool(v)
	case isExactly(t, types.IntType):
		return c.MkAnd(ts.IsInt(v), c.MkNot(ts.CheckIntOverflow(ts.GetInt(v))))
	case isExactly(t, types.UintType):
		return c.MkAnd(ts.IsUint(v), c.MkNot(ts.CheckUintOverflow(ts.GetUint(v))))
	case isExactly(t, types.DoubleType):
		return c.MkAnd(ts.IsDouble(v),
			c.MkImplies(c.MkFPIsNaN(ts.GetDouble(v)), c.MkEq(v, ts.WrapDouble(ts.GetDouble(v)))))
	case isExactly(t, types.StringType):
		return ts.IsString(v)
	case isExactly(t, types.BytesType):
		return ts.IsBytes(v)
	case isExactly(t, types.TimestampType):
		return c.MkAnd(ts.IsTimestamp(v), c.MkNot(ts.CheckTimestampOverflow(ts.GetTimestamp(v))))
	case isExactly(t, types.DurationType):
		return c.MkAnd(ts.IsDuration(v), c.MkNot(ts.CheckDurationOverflow(ts.GetDuration(v))))
	case t.Kind() == types.DynKind || t.Kind() == types.AnyKind:
		return ts.isValidScalar(v)
	case t.Kind() == types.ListKind:
		isList := ts.IsList(v)
		elemType := listElemType(t)
		seq := ts.GetSeq(ts.GetListRef(v))
		length := c.MkLength(seq)
		parts := []*smt.Term{isList}
		if isStaticallyKnown(elemType) {
			parts = append(parts, c.MkImplies(c.MkGt(length, c.MkInt(int64(g.unrollLimit))), ts.hasTruncatedTypeConstraint(v)))
		}
		for i := 0; i < g.unrollLimit; i++ {
			idx := c.MkInt(int64(i))
			elem := c.MkNth(seq, idx)
			valid := c.MkLt(idx, length)
			parts = append(parts, c.MkImplies(valid, c.MkNot(ts.IsErrorOrUnknown(elem))))
			parts = append(parts, c.MkImplies(valid, g.forType(elem, elemType)))
		}
		return MkAndFlattened(c, parts...)
	case t.Kind() == types.MapKind:
		isMap := ts.IsMap(v)
		keyType, valType := mapKeyType(t), mapValueType(t)
		ref := ts.GetMapRef(v)
		seq := ts.GetMapKeys(ref)
		length := c.MkLength(seq)
		values := ts.GetMapValues(ref)
		presence := ts.GetMapPresence(ref)
		parts := []*smt.Term{isMap, g.boundedMapBijection(presence, seq, length)}
		if isStaticallyKnown(keyType) || isStaticallyKnown(valType) {
			parts = append(parts, c.MkImplies(c.MkGt(length, c.MkInt(int64(g.unrollLimit))), ts.hasTruncatedTypeConstraint(v)))
		}
		for i := 0; i < g.unrollLimit; i++ {
			idx := c.MkInt(int64(i))
			key := c.MkNth(seq, idx)
			valid := c.MkLt(idx, length)
			parts = append(parts, c.MkImplies(valid, c.MkAnd(ts.IsPrimitiveKey(key), c.MkNot(ts.IsError(key)))))
			parts = append(parts, c.MkImplies(valid, g.forType(key, keyType)))
			present := c.MkSelect(presence, key)
			validEntry := c.MkAnd(valid, present)
			val := c.MkSelect(values, key)
			parts = append(parts, c.MkImplies(validEntry, c.MkNot(ts.IsErrorOrUnknown(val))))
			parts = append(parts, c.MkImplies(validEntry, g.forType(val, valType)))
		}
		return MkAndFlattened(c, parts...)
	case t.Kind() == types.StructKind:
		return c.MkAnd(ts.IsMessage(v), c.MkEq(ts.GetMsgTypeName(ts.GetMessageRef(v)), MkZ3String(c, t.TypeName())))
	}
	return c.MkTrue()
}

func (g *typeConstraintGenerator) boundedMapBijection(presence, seq, length *smt.Term) *smt.Term {
	c, ts := g.c, g.ts
	var parts []*smt.Term
	for i := 0; i < g.unrollLimit; i++ {
		for j := i + 1; j < g.unrollLimit; j++ {
			validPair := c.MkLt(c.MkInt(int64(j)), length)
			notEqual := c.MkNot(c.MkEq(c.MkNth(seq, c.MkInt(int64(i))), c.MkNth(seq, c.MkInt(int64(j)))))
			parts = append(parts, c.MkImplies(validPair, notEqual))
		}
	}
	notTruncated := c.MkLe(length, c.MkInt(int64(g.unrollLimit)))
	seqMap := c.MkConstArray(ts.celValueSort, c.MkFalse())
	for i := 0; i < g.unrollLimit; i++ {
		seqMap = c.MkITE(c.MkLt(c.MkInt(int64(i)), length), c.MkStore(seqMap, c.MkNth(seq, c.MkInt(int64(i))), c.MkTrue()), seqMap)
	}
	parts = append(parts, c.MkImplies(notTruncated, c.MkEq(presence, seqMap)))
	return MkAndFlattened(c, parts...)
}
