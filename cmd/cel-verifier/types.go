package main

import (
	"fmt"
	"strings"

	"cel.dev/cel-go/cel"
)

// variable is a declared input of the checked expressions.
type variable struct {
	name string
	typ  *cel.Type
}

// parseVariables parses name:type specifications, e.g. x:int or m:map<string, list<int>>.
func parseVariables(specs []string) ([]variable, error) {
	var out []variable
	index := map[string]int{}
	for _, spec := range specs {
		name, typ, ok := strings.Cut(spec, ":")
		if !ok {
			return nil, fmt.Errorf("Invalid variable specification: '%s'. Expected format 'name:type' (e.g., 'x:int').", spec)
		}
		name = strings.TrimSpace(name)
		if name == "" {
			return nil, fmt.Errorf("Invalid variable specification: '%s'. Variable name cannot be empty.", spec)
		}
		t, err := parseType(strings.ToLower(strings.TrimSpace(typ)))
		if err != nil {
			return nil, err
		}
		if i, ok := index[name]; ok {
			out[i].typ = t
			continue
		}
		index[name] = len(out)
		out = append(out, variable{name, t})
	}
	return out, nil
}

func parseType(spec string) (*cel.Type, error) {
	s := strings.ToLower(strings.TrimSpace(spec))
	if inner, ok := generic(s, "list"); ok {
		e, err := parseType(inner)
		if err != nil {
			return nil, err
		}
		return cel.ListType(e), nil
	}
	if inner, ok := generic(s, "map"); ok {
		args := splitGenericArgs(inner)
		if len(args) != 2 {
			return nil, fmt.Errorf("Invalid map type format: '%s'. Expected format 'map<key_type, value_type>' (e.g., 'map<string, int>').", spec)
		}
		k, err := parseType(args[0])
		if err != nil {
			return nil, err
		}
		v, err := parseType(args[1])
		if err != nil {
			return nil, err
		}
		return cel.MapType(k, v), nil
	}
	for _, prefix := range []string{"optional", "optional_type"} {
		if inner, ok := generic(s, prefix); ok {
			e, err := parseType(inner)
			if err != nil {
				return nil, err
			}
			return cel.OptionalType(e), nil
		}
	}
	switch s {
	case "int":
		return cel.IntType, nil
	case "uint":
		return cel.UintType, nil
	case "string":
		return cel.StringType, nil
	case "bool", "boolean":
		return cel.BoolType, nil
	case "double", "float":
		return cel.DoubleType, nil
	case "bytes":
		return cel.BytesType, nil
	case "dyn", "google.protobuf.value":
		return cel.DynType, nil
	case "timestamp", "google.protobuf.timestamp":
		return cel.TimestampType, nil
	case "duration", "google.protobuf.duration":
		return cel.DurationType, nil
	case "google.protobuf.struct":
		return cel.MapType(cel.StringType, cel.DynType), nil
	case "google.protobuf.listvalue":
		return cel.ListType(cel.DynType), nil
	case "google.protobuf.boolvalue":
		return cel.NullableType(cel.BoolType), nil
	case "google.protobuf.bytesvalue":
		return cel.NullableType(cel.BytesType), nil
	case "google.protobuf.doublevalue", "google.protobuf.floatvalue":
		return cel.NullableType(cel.DoubleType), nil
	case "google.protobuf.int32value", "google.protobuf.int64value":
		return cel.NullableType(cel.IntType), nil
	case "google.protobuf.uint32value", "google.protobuf.uint64value":
		return cel.NullableType(cel.UintType), nil
	case "google.protobuf.stringvalue":
		return cel.NullableType(cel.StringType), nil
	}
	return nil, fmt.Errorf("Unsupported type for CLI variable declaration: '%s'. Supported types: int, uint, string, bool, double, bytes, dyn, timestamp, duration, list<T>, map<K, V>, optional<T>.", spec)
}

func generic(s, name string) (string, bool) {
	if strings.HasPrefix(s, name+"<") && strings.HasSuffix(s, ">") {
		return strings.TrimSpace(s[len(name)+1 : len(s)-1]), true
	}
	return "", false
}

func splitGenericArgs(inner string) []string {
	var out []string
	depth, start := 0, 0
	for i, c := range inner {
		switch c {
		case '<':
			depth++
		case '>':
			depth--
		case ',':
			if depth == 0 {
				out = append(out, strings.TrimSpace(inner[start:i]))
				start = i + 1
			}
		}
	}
	if rest := strings.TrimSpace(inner[start:]); rest != "" || start > 0 {
		out = append(out, rest)
	}
	return out
}
