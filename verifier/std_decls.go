// Code generated from testdata/golden/axiom_decls.json (dumped from cel-java); DO NOT EDIT.

package verifier

import "cel.dev/cel-go/common/types"

// standardDecls are the declarations of the standard axioms, with overloads in
// cel-java order, which determines the order of the overload if-then-else chains.
var standardDecls = map[string]FunctionDecl{
	"_+_": {Name: "_+_", Overloads: []OverloadDecl{
		{ID: "add_int64", Params: []*types.Type{types.IntType, types.IntType}, Result: types.IntType},
		{ID: "add_uint64", Params: []*types.Type{types.UintType, types.UintType}, Result: types.UintType},
		{ID: "add_double", Params: []*types.Type{types.DoubleType, types.DoubleType}, Result: types.DoubleType},
		{ID: "add_string", Params: []*types.Type{types.StringType, types.StringType}, Result: types.StringType},
		{ID: "add_bytes", Params: []*types.Type{types.BytesType, types.BytesType}, Result: types.BytesType},
		{ID: "add_list", Params: []*types.Type{types.NewListType(types.DynType), types.NewListType(types.DynType)}, Result: types.NewListType(types.DynType)},
		{ID: "add_timestamp_duration", Params: []*types.Type{types.TimestampType, types.DurationType}, Result: types.TimestampType},
		{ID: "add_duration_timestamp", Params: []*types.Type{types.DurationType, types.TimestampType}, Result: types.TimestampType},
		{ID: "add_duration_duration", Params: []*types.Type{types.DurationType, types.DurationType}, Result: types.DurationType},
	}},
	"_-_": {Name: "_-_", Overloads: []OverloadDecl{
		{ID: "subtract_int64", Params: []*types.Type{types.IntType, types.IntType}, Result: types.IntType},
		{ID: "subtract_uint64", Params: []*types.Type{types.UintType, types.UintType}, Result: types.UintType},
		{ID: "subtract_double", Params: []*types.Type{types.DoubleType, types.DoubleType}, Result: types.DoubleType},
		{ID: "subtract_timestamp_timestamp", Params: []*types.Type{types.TimestampType, types.TimestampType}, Result: types.DurationType},
		{ID: "subtract_timestamp_duration", Params: []*types.Type{types.TimestampType, types.DurationType}, Result: types.TimestampType},
		{ID: "subtract_duration_duration", Params: []*types.Type{types.DurationType, types.DurationType}, Result: types.DurationType},
	}},
	"_*_": {Name: "_*_", Overloads: []OverloadDecl{
		{ID: "multiply_int64", Params: []*types.Type{types.IntType, types.IntType}, Result: types.IntType},
		{ID: "multiply_uint64", Params: []*types.Type{types.UintType, types.UintType}, Result: types.UintType},
		{ID: "multiply_double", Params: []*types.Type{types.DoubleType, types.DoubleType}, Result: types.DoubleType},
	}},
	"_/_": {Name: "_/_", Overloads: []OverloadDecl{
		{ID: "divide_int64", Params: []*types.Type{types.IntType, types.IntType}, Result: types.IntType},
		{ID: "divide_uint64", Params: []*types.Type{types.UintType, types.UintType}, Result: types.UintType},
		{ID: "divide_double", Params: []*types.Type{types.DoubleType, types.DoubleType}, Result: types.DoubleType},
	}},
	"_%_": {Name: "_%_", Overloads: []OverloadDecl{
		{ID: "modulo_int64", Params: []*types.Type{types.IntType, types.IntType}, Result: types.IntType},
		{ID: "modulo_uint64", Params: []*types.Type{types.UintType, types.UintType}, Result: types.UintType},
	}},
	"-_": {Name: "-_", Overloads: []OverloadDecl{
		{ID: "negate_int64", Params: []*types.Type{types.IntType}, Result: types.IntType},
		{ID: "negate_double", Params: []*types.Type{types.DoubleType}, Result: types.DoubleType},
	}},
	"cel.@mapInsert": {Name: "cel.@mapInsert", Overloads: []OverloadDecl{
		{ID: "@mapInsert_map_map", Params: []*types.Type{types.NewMapType(types.DynType, types.DynType), types.NewMapType(types.DynType, types.DynType)}, Result: types.NewMapType(types.DynType, types.DynType)},
		{ID: "@mapInsert_map_key_value", Params: []*types.Type{types.NewMapType(types.DynType, types.DynType), types.NewTypeParamType("K"), types.NewTypeParamType("V")}, Result: types.NewMapType(types.DynType, types.DynType)},
	}},
	"type": {Name: "type", Overloads: []OverloadDecl{
		{ID: "type", Params: []*types.Type{types.NewTypeParamType("A")}, Result: types.NewTypeTypeWithParam(types.DynType)},
	}},
	"@in": {Name: "@in", Overloads: []OverloadDecl{
		{ID: "in_list", Params: []*types.Type{types.NewTypeParamType("A"), types.NewListType(types.DynType)}, Result: types.BoolType},
		{ID: "in_map", Params: []*types.Type{types.NewTypeParamType("A"), types.NewMapType(types.DynType, types.DynType)}, Result: types.BoolType},
	}},
	"_<_": {Name: "_<_", Overloads: []OverloadDecl{
		{ID: "less_bool", Params: []*types.Type{types.BoolType, types.BoolType}, Result: types.BoolType},
		{ID: "less_int64", Params: []*types.Type{types.IntType, types.IntType}, Result: types.BoolType},
		{ID: "less_uint64", Params: []*types.Type{types.UintType, types.UintType}, Result: types.BoolType},
		{ID: "less_double", Params: []*types.Type{types.DoubleType, types.DoubleType}, Result: types.BoolType},
		{ID: "less_string", Params: []*types.Type{types.StringType, types.StringType}, Result: types.BoolType},
		{ID: "less_bytes", Params: []*types.Type{types.BytesType, types.BytesType}, Result: types.BoolType},
		{ID: "less_timestamp", Params: []*types.Type{types.TimestampType, types.TimestampType}, Result: types.BoolType},
		{ID: "less_duration", Params: []*types.Type{types.DurationType, types.DurationType}, Result: types.BoolType},
		{ID: "less_int64_uint64", Params: []*types.Type{types.IntType, types.UintType}, Result: types.BoolType},
		{ID: "less_uint64_int64", Params: []*types.Type{types.UintType, types.IntType}, Result: types.BoolType},
		{ID: "less_int64_double", Params: []*types.Type{types.IntType, types.DoubleType}, Result: types.BoolType},
		{ID: "less_double_int64", Params: []*types.Type{types.DoubleType, types.IntType}, Result: types.BoolType},
		{ID: "less_uint64_double", Params: []*types.Type{types.UintType, types.DoubleType}, Result: types.BoolType},
		{ID: "less_double_uint64", Params: []*types.Type{types.DoubleType, types.UintType}, Result: types.BoolType},
	}},
	"_<=_": {Name: "_<=_", Overloads: []OverloadDecl{
		{ID: "less_equals_bool", Params: []*types.Type{types.BoolType, types.BoolType}, Result: types.BoolType},
		{ID: "less_equals_int64", Params: []*types.Type{types.IntType, types.IntType}, Result: types.BoolType},
		{ID: "less_equals_uint64", Params: []*types.Type{types.UintType, types.UintType}, Result: types.BoolType},
		{ID: "less_equals_double", Params: []*types.Type{types.DoubleType, types.DoubleType}, Result: types.BoolType},
		{ID: "less_equals_string", Params: []*types.Type{types.StringType, types.StringType}, Result: types.BoolType},
		{ID: "less_equals_bytes", Params: []*types.Type{types.BytesType, types.BytesType}, Result: types.BoolType},
		{ID: "less_equals_timestamp", Params: []*types.Type{types.TimestampType, types.TimestampType}, Result: types.BoolType},
		{ID: "less_equals_duration", Params: []*types.Type{types.DurationType, types.DurationType}, Result: types.BoolType},
		{ID: "less_equals_int64_uint64", Params: []*types.Type{types.IntType, types.UintType}, Result: types.BoolType},
		{ID: "less_equals_uint64_int64", Params: []*types.Type{types.UintType, types.IntType}, Result: types.BoolType},
		{ID: "less_equals_int64_double", Params: []*types.Type{types.IntType, types.DoubleType}, Result: types.BoolType},
		{ID: "less_equals_double_int64", Params: []*types.Type{types.DoubleType, types.IntType}, Result: types.BoolType},
		{ID: "less_equals_uint64_double", Params: []*types.Type{types.UintType, types.DoubleType}, Result: types.BoolType},
		{ID: "less_equals_double_uint64", Params: []*types.Type{types.DoubleType, types.UintType}, Result: types.BoolType},
	}},
	"_>_": {Name: "_>_", Overloads: []OverloadDecl{
		{ID: "greater_bool", Params: []*types.Type{types.BoolType, types.BoolType}, Result: types.BoolType},
		{ID: "greater_int64", Params: []*types.Type{types.IntType, types.IntType}, Result: types.BoolType},
		{ID: "greater_uint64", Params: []*types.Type{types.UintType, types.UintType}, Result: types.BoolType},
		{ID: "greater_double", Params: []*types.Type{types.DoubleType, types.DoubleType}, Result: types.BoolType},
		{ID: "greater_string", Params: []*types.Type{types.StringType, types.StringType}, Result: types.BoolType},
		{ID: "greater_bytes", Params: []*types.Type{types.BytesType, types.BytesType}, Result: types.BoolType},
		{ID: "greater_timestamp", Params: []*types.Type{types.TimestampType, types.TimestampType}, Result: types.BoolType},
		{ID: "greater_duration", Params: []*types.Type{types.DurationType, types.DurationType}, Result: types.BoolType},
		{ID: "greater_int64_uint64", Params: []*types.Type{types.IntType, types.UintType}, Result: types.BoolType},
		{ID: "greater_uint64_int64", Params: []*types.Type{types.UintType, types.IntType}, Result: types.BoolType},
		{ID: "greater_int64_double", Params: []*types.Type{types.IntType, types.DoubleType}, Result: types.BoolType},
		{ID: "greater_double_int64", Params: []*types.Type{types.DoubleType, types.IntType}, Result: types.BoolType},
		{ID: "greater_uint64_double", Params: []*types.Type{types.UintType, types.DoubleType}, Result: types.BoolType},
		{ID: "greater_double_uint64", Params: []*types.Type{types.DoubleType, types.UintType}, Result: types.BoolType},
	}},
	"_>=_": {Name: "_>=_", Overloads: []OverloadDecl{
		{ID: "greater_equals_bool", Params: []*types.Type{types.BoolType, types.BoolType}, Result: types.BoolType},
		{ID: "greater_equals_int64", Params: []*types.Type{types.IntType, types.IntType}, Result: types.BoolType},
		{ID: "greater_equals_uint64", Params: []*types.Type{types.UintType, types.UintType}, Result: types.BoolType},
		{ID: "greater_equals_double", Params: []*types.Type{types.DoubleType, types.DoubleType}, Result: types.BoolType},
		{ID: "greater_equals_string", Params: []*types.Type{types.StringType, types.StringType}, Result: types.BoolType},
		{ID: "greater_equals_bytes", Params: []*types.Type{types.BytesType, types.BytesType}, Result: types.BoolType},
		{ID: "greater_equals_timestamp", Params: []*types.Type{types.TimestampType, types.TimestampType}, Result: types.BoolType},
		{ID: "greater_equals_duration", Params: []*types.Type{types.DurationType, types.DurationType}, Result: types.BoolType},
		{ID: "greater_equals_int64_uint64", Params: []*types.Type{types.IntType, types.UintType}, Result: types.BoolType},
		{ID: "greater_equals_uint64_int64", Params: []*types.Type{types.UintType, types.IntType}, Result: types.BoolType},
		{ID: "greater_equals_int64_double", Params: []*types.Type{types.IntType, types.DoubleType}, Result: types.BoolType},
		{ID: "greater_equals_double_int64", Params: []*types.Type{types.DoubleType, types.IntType}, Result: types.BoolType},
		{ID: "greater_equals_uint64_double", Params: []*types.Type{types.UintType, types.DoubleType}, Result: types.BoolType},
		{ID: "greater_equals_double_uint64", Params: []*types.Type{types.DoubleType, types.UintType}, Result: types.BoolType},
	}},
	"size": {Name: "size", Overloads: []OverloadDecl{
		{ID: "size_string", Params: []*types.Type{types.StringType}, Result: types.IntType},
		{ID: "size_bytes", Params: []*types.Type{types.BytesType}, Result: types.IntType},
		{ID: "size_list", Params: []*types.Type{types.NewListType(types.DynType)}, Result: types.IntType},
		{ID: "size_map", Params: []*types.Type{types.NewMapType(types.DynType, types.DynType)}, Result: types.IntType},
		{ID: "string_size", Params: []*types.Type{types.StringType}, Result: types.IntType},
		{ID: "bytes_size", Params: []*types.Type{types.BytesType}, Result: types.IntType},
		{ID: "list_size", Params: []*types.Type{types.NewListType(types.DynType)}, Result: types.IntType},
		{ID: "map_size", Params: []*types.Type{types.NewMapType(types.DynType, types.DynType)}, Result: types.IntType},
	}},
	"optional.none": {Name: "optional.none", Overloads: []OverloadDecl{
		{ID: "optional_none", Params: []*types.Type{}, Result: types.NewOptionalType(types.DynType)},
	}},
	"optional.of": {Name: "optional.of", Overloads: []OverloadDecl{
		{ID: "optional_of", Params: []*types.Type{types.NewTypeParamType("V")}, Result: types.NewOptionalType(types.DynType)},
	}},
	"optional.ofNonZeroValue": {Name: "optional.ofNonZeroValue", Overloads: []OverloadDecl{
		{ID: "optional_ofNonZeroValue", Params: []*types.Type{types.NewTypeParamType("V")}, Result: types.NewOptionalType(types.DynType)},
	}},
	"hasValue": {Name: "hasValue", Overloads: []OverloadDecl{
		{ID: "optional_hasValue", Params: []*types.Type{types.NewOptionalType(types.DynType)}, Result: types.BoolType},
	}},
	"value": {Name: "value", Overloads: []OverloadDecl{
		{ID: "optional_value", Params: []*types.Type{types.NewOptionalType(types.DynType)}, Result: types.NewTypeParamType("V")},
	}},
	"orValue": {Name: "orValue", Overloads: []OverloadDecl{
		{ID: "optional_orValue_value", Params: []*types.Type{types.NewOptionalType(types.DynType), types.NewTypeParamType("V")}, Result: types.NewTypeParamType("V")},
	}},
	"or": {Name: "or", Overloads: []OverloadDecl{
		{ID: "optional_or_optional", Params: []*types.Type{types.NewOptionalType(types.DynType), types.NewOptionalType(types.DynType)}, Result: types.NewOptionalType(types.DynType)},
	}},
	"_?._": {Name: "_?._", Overloads: []OverloadDecl{
		{ID: "select_optional_field", Params: []*types.Type{types.DynType, types.StringType}, Result: types.NewOptionalType(types.DynType)},
	}},
	"contains": {Name: "contains", Overloads: []OverloadDecl{
		{ID: "contains_string", Params: []*types.Type{types.StringType, types.StringType}, Result: types.BoolType},
	}},
	"startsWith": {Name: "startsWith", Overloads: []OverloadDecl{
		{ID: "starts_with_string", Params: []*types.Type{types.StringType, types.StringType}, Result: types.BoolType},
	}},
	"endsWith": {Name: "endsWith", Overloads: []OverloadDecl{
		{ID: "ends_with_string", Params: []*types.Type{types.StringType, types.StringType}, Result: types.BoolType},
	}},
	"int": {Name: "int", Overloads: []OverloadDecl{
		{ID: "int64_to_int64", Params: []*types.Type{types.IntType}, Result: types.IntType},
		{ID: "uint64_to_int64", Params: []*types.Type{types.UintType}, Result: types.IntType},
		{ID: "double_to_int64", Params: []*types.Type{types.DoubleType}, Result: types.IntType},
		{ID: "string_to_int64", Params: []*types.Type{types.StringType}, Result: types.IntType},
		{ID: "timestamp_to_int64", Params: []*types.Type{types.TimestampType}, Result: types.IntType},
	}},
	"uint": {Name: "uint", Overloads: []OverloadDecl{
		{ID: "uint64_to_uint64", Params: []*types.Type{types.UintType}, Result: types.UintType},
		{ID: "int64_to_uint64", Params: []*types.Type{types.IntType}, Result: types.UintType},
		{ID: "double_to_uint64", Params: []*types.Type{types.DoubleType}, Result: types.UintType},
		{ID: "string_to_uint64", Params: []*types.Type{types.StringType}, Result: types.UintType},
	}},
	"double": {Name: "double", Overloads: []OverloadDecl{
		{ID: "double_to_double", Params: []*types.Type{types.DoubleType}, Result: types.DoubleType},
		{ID: "int64_to_double", Params: []*types.Type{types.IntType}, Result: types.DoubleType},
		{ID: "uint64_to_double", Params: []*types.Type{types.UintType}, Result: types.DoubleType},
		{ID: "string_to_double", Params: []*types.Type{types.StringType}, Result: types.DoubleType},
	}},
	"string": {Name: "string", Overloads: []OverloadDecl{
		{ID: "string_to_string", Params: []*types.Type{types.StringType}, Result: types.StringType},
		{ID: "int64_to_string", Params: []*types.Type{types.IntType}, Result: types.StringType},
		{ID: "uint64_to_string", Params: []*types.Type{types.UintType}, Result: types.StringType},
		{ID: "double_to_string", Params: []*types.Type{types.DoubleType}, Result: types.StringType},
		{ID: "bool_to_string", Params: []*types.Type{types.BoolType}, Result: types.StringType},
		{ID: "bytes_to_string", Params: []*types.Type{types.BytesType}, Result: types.StringType},
		{ID: "timestamp_to_string", Params: []*types.Type{types.TimestampType}, Result: types.StringType},
		{ID: "duration_to_string", Params: []*types.Type{types.DurationType}, Result: types.StringType},
	}},
	"bytes": {Name: "bytes", Overloads: []OverloadDecl{
		{ID: "bytes_to_bytes", Params: []*types.Type{types.BytesType}, Result: types.BytesType},
		{ID: "string_to_bytes", Params: []*types.Type{types.StringType}, Result: types.BytesType},
	}},
	"dyn": {Name: "dyn", Overloads: []OverloadDecl{
		{ID: "to_dyn", Params: []*types.Type{types.NewTypeParamType("A")}, Result: types.DynType},
	}},
	"duration": {Name: "duration", Overloads: []OverloadDecl{
		{ID: "duration_to_duration", Params: []*types.Type{types.DurationType}, Result: types.DurationType},
		{ID: "string_to_duration", Params: []*types.Type{types.StringType}, Result: types.DurationType},
	}},
	"timestamp": {Name: "timestamp", Overloads: []OverloadDecl{
		{ID: "string_to_timestamp", Params: []*types.Type{types.StringType}, Result: types.TimestampType},
		{ID: "timestamp_to_timestamp", Params: []*types.Type{types.TimestampType}, Result: types.TimestampType},
		{ID: "int64_to_timestamp", Params: []*types.Type{types.IntType}, Result: types.TimestampType},
	}},
	"bool": {Name: "bool", Overloads: []OverloadDecl{
		{ID: "bool_to_bool", Params: []*types.Type{types.BoolType}, Result: types.BoolType},
		{ID: "string_to_bool", Params: []*types.Type{types.StringType}, Result: types.BoolType},
	}},
}
