package verifier

import (
	"cel.dev/cel-go/common/ast"
	"cel.dev/cel-go/common/types"
)

// Helpers mirroring the cel-java type model on top of cel-go types.

const (
	optionalTypeName = "optional_type"

	valueMessage     = "google.protobuf.Value"
	listValueMessage = "google.protobuf.ListValue"
	structMessage    = "google.protobuf.Struct"
	anyMessage       = "google.protobuf.Any"
	timestampMessage = "google.protobuf.Timestamp"
	durationMessage  = "google.protobuf.Duration"

	boolWrapper   = "google.protobuf.BoolValue"
	bytesWrapper  = "google.protobuf.BytesValue"
	doubleWrapper = "google.protobuf.DoubleValue"
	floatWrapper  = "google.protobuf.FloatValue"
	int32Wrapper  = "google.protobuf.Int32Value"
	int64Wrapper  = "google.protobuf.Int64Value"
	stringWrapper = "google.protobuf.StringValue"
	uint32Wrapper = "google.protobuf.UInt32Value"
	uint64Wrapper = "google.protobuf.UInt64Value"
)

var wrapperTargets = map[string]*types.Type{
	boolWrapper:   types.BoolType,
	bytesWrapper:  types.BytesType,
	doubleWrapper: types.DoubleType,
	floatWrapper:  types.DoubleType,
	int32Wrapper:  types.IntType,
	int64Wrapper:  types.IntType,
	stringWrapper: types.StringType,
	uint32Wrapper: types.UintType,
	uint64Wrapper: types.UintType,
}

func isWrapperType(name string) bool { _, ok := wrapperTargets[name]; return ok }

func isWellKnownType(name string) bool {
	if isWrapperType(name) {
		return true
	}
	switch name {
	case anyMessage, durationMessage, timestampMessage, listValueMessage, structMessage, valueMessage:
		return true
	}
	return false
}

func isPrimitiveKind(k types.Kind) bool {
	switch k {
	case types.BoolKind, types.IntKind, types.UintKind, types.DoubleKind, types.StringKind, types.BytesKind:
		return true
	}
	return false
}

// isNullable reports whether t is a wrapper (nullable primitive) type.
func isNullable(t *types.Type) bool {
	return t != nil && isPrimitiveKind(t.Kind()) && t.IsAssignableType(types.NullType)
}

// nullableTarget returns the primitive type a nullable type wraps.
func nullableTarget(t *types.Type) *types.Type {
	switch t.Kind() {
	case types.BoolKind:
		return types.BoolType
	case types.IntKind:
		return types.IntType
	case types.UintKind:
		return types.UintType
	case types.DoubleKind:
		return types.DoubleType
	case types.StringKind:
		return types.StringType
	case types.BytesKind:
		return types.BytesType
	}
	return t
}

func isOptionalType(t *types.Type) bool {
	return t != nil && t.Kind() == types.OpaqueKind && t.TypeName() == optionalTypeName
}

// typeEquals compares types the way cel-java's CelType.equals does.
func typeEquals(a, b *types.Type) bool {
	if a == nil || b == nil {
		return a == b
	}
	if a.Kind() != b.Kind() || isNullable(a) != isNullable(b) || a.TypeName() != b.TypeName() {
		return false
	}
	pa, pb := a.Parameters(), b.Parameters()
	if len(pa) != len(pb) {
		return false
	}
	for i := range pa {
		if !typeEquals(pa[i], pb[i]) {
			return false
		}
	}
	return true
}

// isExactly reports whether t is exactly the (non-nullable) simple type s.
func isExactly(t, s *types.Type) bool { return typeEquals(t, s) }

func isDynKind(k types.Kind) bool { return k == types.DynKind || k == types.AnyKind }

// isStaticallyKnown reports whether t itself is neither dyn nor a type parameter.
// Unlike isConcrete, its type parameters may still be (e.g. list(dyn)).
func isStaticallyKnown(t *types.Type) bool {
	k := t.Kind()
	return !isDynKind(k) && k != types.TypeParamKind
}

// isConcrete reports whether t and, recursively, its type parameters are statically known.
func isConcrete(t *types.Type) bool {
	if !isStaticallyKnown(t) {
		return false
	}
	for _, p := range t.Parameters() {
		if !isConcrete(p) {
			return false
		}
	}
	return true
}

// hasConcreteElements reports whether t is a list or map whose elements (or keys) are concrete.
func hasConcreteElements(t *types.Type) bool {
	return (t.Kind() == types.ListKind || t.Kind() == types.MapKind) && isConcrete(t.Parameters()[0])
}

// hasStructuralEquality reports whether values of t are equal exactly when their terms are.
func hasStructuralEquality(t *types.Type) bool {
	switch t.Kind() {
	case types.BoolKind, types.IntKind, types.UintKind, types.StringKind, types.BytesKind,
		types.TimestampKind, types.DurationKind:
		return true
	case types.ListKind, types.MapKind:
		for _, p := range t.Parameters() {
			if !hasStructuralEquality(p) {
				return false
			}
		}
		return true
	}
	return false
}

func isNumericType(t *types.Type) bool {
	switch t.Kind() {
	case types.IntKind, types.UintKind, types.DoubleKind:
		return true
	}
	return false
}

func listElemType(t *types.Type) *types.Type { return t.Parameters()[0] }
func mapKeyType(t *types.Type) *types.Type   { return t.Parameters()[0] }
func mapValueType(t *types.Type) *types.Type { return t.Parameters()[1] }

// exprType returns the checked type of e, or dyn.
func exprType(a *ast.AST, e ast.Expr) *types.Type {
	if e == nil {
		return types.DynType
	}
	if t, ok := a.TypeMap()[e.ID()]; ok && t != nil {
		return t
	}
	return types.DynType
}
