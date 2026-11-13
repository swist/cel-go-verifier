package verifier

import (
	"math"

	"cel.dev/cel-go/common/ast"
	"cel.dev/cel-go/common/types"

	"github.com/swist/cel-go-verifier/smt"
)

// TypeProvider describes the message types the verifier models.
type TypeProvider interface {
	// StructTypeNames lists the message types, in a stable order.
	StructTypeNames() []string
	// FieldType returns the type of a field of a message type.
	FieldType(message, field string) (*types.Type, bool)
}

const maxUint32 = 0xFFFFFFFF

// structTranslator translates message construction and field selection.
type structTranslator struct {
	x            *translationContext
	c            *smt.Context
	ts           *TypeSystem
	tcg          *typeConstraintGenerator
	tp           TypeProvider
	tr           *astTranslator
	emptyMsg     map[string]*smt.Term
	emptyList    *smt.Term
	emptyMap     *smt.Term
}

func (st *structTranslator) translateStruct(e ast.Expr, a *ast.AST) tv {
	c, ts := st.c, st.ts
	s := e.AsStruct()
	name := s.TypeName()
	switch {
	case name == valueMessage || name == listValueMessage || name == structMessage:
		return st.translateJSONWkt(e, a)
	case isWrapperType(name):
		return st.translateWrapper(e, a)
	case name == timestampMessage:
		return st.translateTimeWkt(e, a, 0, func(seconds, nanos, total *smt.Term) *smt.Term {
			return ts.WithRuntimeError(ts.WrapTimestamp(total), ts.CheckTimestampOverflow(total))
		})
	case name == durationMessage:
		return st.translateTimeWkt(e, a, -maxNanos, func(seconds, nanos, total *smt.Term) *smt.Term {
			signMismatch := c.MkOr(
				c.MkAnd(c.MkGt(seconds, c.MkInt(0)), c.MkLt(nanos, c.MkInt(0))),
				c.MkAnd(c.MkLt(seconds, c.MkInt(0)), c.MkGt(nanos, c.MkInt(0))))
			return ts.WithRuntimeError(ts.WrapDuration(total), signMismatch, ts.CheckDurationOverflow(total))
		})
	}
	if len(s.Fields()) == 0 {
		return tv{st.defaultValue(types.NewObjectType(name)), e, c.MkFalse()}
	}
	msgRef := ts.MkMessageRefConst("!msg_ref")
	values := c.MkConstArray(c.StringSort(), ts.MkUnknown())
	presence := c.MkConstArray(c.StringSort(), c.MkFalse())
	var elems []tv
	var invalid []*smt.Term
	fields := map[string]bool{}
	for _, f := range s.Fields() {
		fe := f.AsStructField()
		key := MkZ3String(c, fe.Name())
		v := st.tr.translateExpr(fe.Value(), a)
		value := v.z3
		fieldType, ok := st.tp.FieldType(name, fe.Name())
		if !ok {
			fieldType = exprType(a, fe.Value())
		}
		finalValue := value
		hasValue := c.MkTrue()
		if fe.IsOptional() {
			checked := ts.WithRuntimeError(value, c.MkNot(ts.IsOptional(value)))
			v = tv{checked, fe.Value(), v.approx}
			ref := ts.GetOptionalRef(checked)
			hasValue = ts.OptHasValue(ref)
			finalValue = ts.GetOptionalValue(ref)
		}
		isUnset := c.MkFalse()
		switch {
		case isPrimitiveKind(fieldType.Kind()):
			isUnset = c.MkEq(finalValue, st.defaultValue(fieldType))
		case fieldType.Kind() == types.ListKind || fieldType.Kind() == types.MapKind:
			isList := fieldType.Kind() == types.ListKind
			hasKind := ts.IsMap(finalValue)
			if isList {
				hasKind = ts.IsList(finalValue)
			}
			invalid = append(invalid, c.MkAnd(hasValue, c.MkNot(hasKind)))
			var elements *smt.Term
			if isList {
				elements = ts.GetSeq(ts.GetListRef(finalValue))
			} else {
				elements = ts.GetMapKeys(ts.GetMapRef(finalValue))
			}
			isEmpty := c.MkAnd(hasKind, c.MkEq(c.MkLength(elements), c.MkInt(0)))
			isUnset = isEmpty
			if typeEquals(fieldType, types.NewListType(types.DynType)) || typeEquals(fieldType, types.NewMapType(types.StringType, types.DynType)) {
				v = v.withApproximation(c, st.x.recordApproximation(
					"whether empty `list(dyn)` and `map(string, dyn)` fields are set",
					MkAndFlattened(c, hasValue, isEmpty)))
				isUnset = c.MkAnd(isEmpty, c.MkBoolConst("!unset_"+name+"."+fe.Name()))
			}
		}
		elems = append(elems, v)
		bypass := c.MkOr(c.MkNot(hasValue), isUnset)
		repeated := fields[fe.Name()]
		fields[fe.Name()] = true
		unsetValues, unsetPresence := values, presence
		if repeated {
			unsetValues = c.MkStore(values, key, ts.MkUnknown())
			unsetPresence = c.MkStore(presence, key, c.MkFalse())
		}
		values = c.MkITE(bypass, unsetValues, c.MkStore(values, key, finalValue))
		presence = c.MkITE(bypass, unsetPresence, c.MkStore(presence, key, c.MkTrue()))
	}
	st.x.addConstraint(c.MkEq(ts.GetMsgTypeName(msgRef), MkZ3String(c, name)))
	st.x.addConstraint(c.MkEq(ts.GetMsgValues(msgRef), values))
	st.x.addConstraint(c.MkEq(ts.GetMsgPresence(msgRef), presence))
	res := ts.WithRuntimeError(ts.WrapMessage(msgRef), MkOrFlattened(c, invalid...))
	return propagateStrictExpr(ts, res, e, elems)
}

func (st *structTranslator) translateJSONWkt(e ast.Expr, a *ast.AST) tv {
	c, ts := st.c, st.ts
	s := e.AsStruct()
	var fallback *smt.Term
	switch s.TypeName() {
	case valueMessage:
		fallback = ts.MkNull()
	case listValueMessage:
		fallback = st.defaultValue(types.NewListType(types.DynType))
	default:
		fallback = st.defaultValue(types.NewMapType(types.StringType, types.DynType))
	}
	if len(s.Fields()) == 0 {
		return tv{fallback, e, c.MkFalse()}
	}
	fe := s.Fields()[0].AsStructField()
	v := st.tr.translateExpr(fe.Value(), a)
	final := v.z3
	isNullValue := s.TypeName() == valueMessage && fe.Name() == "null_value"
	if fe.IsOptional() {
		checked := ts.WithRuntimeError(final, c.MkNot(ts.IsOptional(final)))
		v = tv{checked, fe.Value(), v.approx}
		ref := ts.GetOptionalRef(checked)
		unpacked := ts.GetOptionalValue(ref)
		if isNullValue {
			unpacked = ts.MkNull()
		}
		final = c.MkITE(ts.OptHasValue(ref), unpacked, fallback)
	} else if isNullValue {
		final = ts.MkNull()
	}
	return propagateStrictExpr(ts, final, e, []tv{v})
}

func (st *structTranslator) translateWrapper(e ast.Expr, a *ast.AST) tv {
	c, ts := st.c, st.ts
	s := e.AsStruct()
	name := s.TypeName()
	target := wrapperTargets[name]
	cur := st.defaultValue(target)
	var elems []tv
	for _, f := range s.Fields() {
		fe := f.AsStructField()
		v := st.tr.translateExpr(fe.Value(), a)
		val := v.z3
		if fe.IsOptional() {
			checked := ts.WithRuntimeError(val, c.MkNot(ts.IsOptional(val)))
			v = tv{checked, fe.Value(), v.approx}
			ref := ts.GetOptionalRef(checked)
			cur = c.MkITE(ts.OptHasValue(ref), ts.GetOptionalValue(ref), cur)
		} else {
			cur = val
		}
		elems = append(elems, v)
	}
	valid := st.tcg.forType(cur, target)
	switch name {
	case int32Wrapper:
		iv := ts.GetInt(cur)
		valid = c.MkAnd(valid, c.MkGe(iv, c.MkInt(math.MinInt32)), c.MkLe(iv, c.MkInt(math.MaxInt32)))
	case uint32Wrapper:
		uv := ts.GetUint(cur)
		valid = c.MkAnd(valid, c.MkGe(uv, c.MkInt(0)), c.MkLe(uv, c.MkInt(maxUint32)))
	case floatWrapper:
		d := ts.GetDouble(cur)
		narrowed := c.MkFPToFP(c.MkFPRoundNearestTiesToEven(), d, c.FPSortSingle())
		widened := c.MkFPToFP(c.MkFPRoundNearestTiesToEven(), narrowed, c.FPSortDouble())
		cur = ts.WrapDouble(widened)
	}
	cur = ts.WithRuntimeError(cur, c.MkNot(valid))
	return propagateStrictExpr(ts, cur, e, elems)
}

func (st *structTranslator) translateTimeWkt(e ast.Expr, a *ast.AST, minNanos int64, factory func(seconds, nanos, total *smt.Term) *smt.Term) tv {
	c, ts := st.c, st.ts
	s := e.AsStruct()
	var elems []tv
	secondsVal := st.resolveField(s, "seconds", ts.MkInt(0), a, &elems)
	nanosVal := st.resolveField(s, "nanos", ts.MkInt(0), a, &elems)
	seconds, nanos := ts.GetInt(secondsVal), ts.GetInt(nanosVal)
	total := c.MkAdd(c.MkMul(seconds, c.MkInt(NanosPerSecond)), nanos)
	typeError := c.MkOr(c.MkNot(ts.IsInt(secondsVal)), c.MkNot(ts.IsInt(nanosVal)))
	nanosOutOfRange := c.MkOr(c.MkLt(nanos, c.MkInt(minNanos)), c.MkGe(nanos, c.MkInt(NanosPerSecond)))
	res := ts.WithRuntimeError(factory(seconds, nanos, total), typeError, nanosOutOfRange)
	return propagateStrictExpr(ts, res, e, elems)
}

func (st *structTranslator) resolveField(s ast.StructExpr, field string, def *smt.Term, a *ast.AST, elems *[]tv) *smt.Term {
	c, ts := st.c, st.ts
	var last ast.StructField
	for _, f := range s.Fields() {
		if f.AsStructField().Name() == field {
			last = f.AsStructField()
		}
	}
	if last == nil {
		return def
	}
	v := st.tr.translateExpr(last.Value(), a)
	val := v.z3
	if last.IsOptional() {
		checked := ts.WithRuntimeError(val, c.MkNot(ts.IsOptional(val)))
		v = tv{checked, last.Value(), v.approx}
		ref := ts.GetOptionalRef(checked)
		val = c.MkITE(ts.OptHasValue(ref), ts.GetOptionalValue(ref), def)
	}
	*elems = append(*elems, v)
	return val
}

// defaultValue is the value of an unset field of type t.
func (st *structTranslator) defaultValue(t *types.Type) *smt.Term {
	c, ts := st.c, st.ts
	switch {
	case isNullable(t):
		return ts.MkNull()
	case isOptionalType(t):
		return ts.MkOptionalNone()
	case t.Kind() == types.IntKind:
		return ts.MkInt(0)
	case isExactly(t, types.BoolType):
		return ts.WrapBool(c.MkFalse())
	case isExactly(t, types.StringType):
		return ts.MkString("")
	case isExactly(t, types.BytesType):
		return ts.MkBytes("")
	case isExactly(t, types.DoubleType):
		return ts.MkDouble(0.0)
	case isExactly(t, types.UintType):
		return ts.MkUint64(0)
	case isExactly(t, types.TimestampType):
		return ts.WrapTimestamp(c.MkInt(0))
	case isExactly(t, types.DurationType):
		return ts.WrapDuration(c.MkInt(0))
	case t.Kind() == types.DynKind:
		return ts.MkNull()
	case t.Kind() == types.AnyKind:
		return ts.MkError()
	case t.Kind() == types.ListKind:
		if st.emptyList == nil {
			st.emptyList = ts.MkListRefConst("!empty_list")
			st.x.addConstraint(c.MkEq(ts.GetSeq(st.emptyList), c.MkEmptySeq(c.SeqSort(ts.celValueSort))))
		}
		return ts.WrapList(st.emptyList)
	case t.Kind() == types.MapKind:
		if st.emptyMap == nil {
			st.emptyMap = ts.MkMapRefConst("!empty_map")
			st.x.addConstraint(c.MkEq(ts.GetMapPresence(st.emptyMap), c.MkConstArray(ts.celValueSort, c.MkFalse())))
			st.x.addConstraint(c.MkEq(ts.GetMapValues(st.emptyMap), c.MkConstArray(ts.celValueSort, ts.MkUnknown())))
			st.x.addConstraint(c.MkEq(ts.GetMapKeys(st.emptyMap), c.MkEmptySeq(c.SeqSort(ts.celValueSort))))
		}
		return ts.WrapMap(st.emptyMap)
	case t.Kind() == types.StructKind:
		name := t.TypeName()
		ref, ok := st.emptyMsg[name]
		if !ok {
			ref = ts.MkMessageRefConst("!empty_msg_ref_" + name)
			st.x.addConstraint(c.MkEq(ts.GetMsgPresence(ref), c.MkConstArray(c.StringSort(), c.MkFalse())))
			st.x.addConstraint(c.MkEq(ts.GetMsgValues(ref), c.MkConstArray(c.StringSort(), ts.MkUnknown())))
			st.x.addConstraint(c.MkEq(ts.GetMsgTypeName(ref), MkZ3String(c, name)))
			st.emptyMsg[name] = ref
		}
		return ts.WrapMessage(ref)
	}
	return ts.MkUnknown()
}

type fieldAccess struct{ presence, value *smt.Term }

func (st *structTranslator) mapAccess(operand *smt.Term, field string, guard *smt.Term) fieldAccess {
	c, ts := st.c, st.ts
	ref := ts.GetMapRef(operand)
	key := ts.MkString(field)
	presence := c.MkSelect(ts.GetMapPresence(ref), key)
	value := c.MkSelect(ts.GetMapValues(ref), key)
	st.x.constrainValidValue(MkAndFlattened(c, guard, presence), value)
	return fieldAccess{presence, value}
}

func (st *structTranslator) msgAccess(operand *smt.Term, field string, guard *smt.Term) fieldAccess {
	c, ts := st.c, st.ts
	ref := ts.GetMessageRef(operand)
	key := MkZ3String(c, field)
	presence := c.MkSelect(ts.GetMsgPresence(ref), key)
	value := c.MkSelect(ts.GetMsgValues(ref), key)
	st.x.constrainValidValue(MkAndFlattened(c, guard, presence), value)
	return fieldAccess{presence, value}
}

func (st *structTranslator) translateSelect(e ast.Expr, a *ast.AST) tv {
	c, ts := st.c, st.ts
	sel := e.AsSelect()
	operandTV := st.tr.translateExpr(sel.Operand(), a)
	operand := operandTV.z3
	field := sel.FieldName()
	operandType := exprType(a, sel.Operand())
	var presenceResult, valueResult *smt.Term
	unmodeledMessage := c.MkFalse()
	presenceError := c.MkFalse()
	switch {
	case operandType.Kind() == types.MapKind:
		acc := st.mapAccess(operand, field, c.MkTrue())
		presenceResult = acc.presence
		valueResult = c.MkITE(acc.presence, acc.value, ts.MkError())
	case operandType.Kind() == types.StructKind:
		acc := st.msgAccess(operand, field, c.MkTrue())
		presenceResult = acc.presence
		valueResult = c.MkITE(acc.presence, acc.value, st.defaultValue(exprType(a, e)))
	default:
		isMap, isMsg := ts.IsMap(operand), ts.IsMessage(operand)
		mapAcc := st.mapAccess(operand, field, isMap)
		msgAcc := st.msgAccess(operand, field, isMsg)
		presenceResult = NewSwitch(c).Case(isMsg, msgAcc.presence).Case(isMap, mapAcc.presence).Build(c.MkFalse())
		typeName := ts.GetMsgTypeName(ts.GetMessageRef(operand))
		msgRead := NewSwitch(c)
		var modeled, undeclared []*smt.Term
		for _, tn := range st.tp.StructTypeNames() {
			if isWellKnownType(tn) {
				continue
			}
			isType := c.MkEq(typeName, MkZ3String(c, tn))
			modeled = append(modeled, isType)
			ft, declared := st.tp.FieldType(tn, field)
			if !declared {
				undeclared = append(undeclared, isType)
				msgRead.Case(isType, ts.MkError())
				continue
			}
			if sel.IsTestOnly() {
				continue
			}
			st.x.addConstraint(c.MkImplies(c.MkAnd(isMsg, isType, msgAcc.presence), st.tcg.forType(msgAcc.value, ft)))
			msgRead.Case(isType, c.MkITE(msgAcc.presence, msgAcc.value, st.defaultValue(ft)))
		}
		unmodeledMessage = st.x.recordApproximation("messages of types the type provider doesn't declare",
			c.MkAnd(isMsg, c.MkNot(MkOrFlattened(c, modeled...))))
		mapRead := c.MkITE(mapAcc.presence, mapAcc.value, ts.MkError())
		presenceError = c.MkOr(c.MkAnd(isMsg, MkOrFlattened(c, undeclared...)), c.MkNot(c.MkOr(isMap, isMsg)))
		valueResult = NewSwitch(c).
			Case(isMsg, msgRead.Build(c.MkITE(msgAcc.presence, msgAcc.value, ts.MkUnknown()))).
			Case(isMap, mapRead).
			Build(ts.MkError())
	}
	access := valueResult
	if sel.IsTestOnly() {
		access = ts.WithRuntimeError(ts.WrapBool(presenceResult), presenceError)
	}
	st.x.addConstraint(st.tcg.createTypeConstraint(access, e, a))
	res := propagateStrictExpr(ts, access, e, []tv{operandTV})
	if operandType.Kind() == types.StructKind {
		return res
	}
	return res.withApproximation(c, MkOrFlattened(c, st.x.isTruncatedMap(operand), unmodeledMessage))
}
