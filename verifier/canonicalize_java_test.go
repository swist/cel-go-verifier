package verifier_test

// Port of cel-java's CanonicalizationOptimizerTest. cel-java compares the
// unparsed canonical AST with the expected text; the unparsers differ, so
// here both the canonical AST and the parsed expected text are printed as
// ID-free trees with macros expanded.

import (
	"fmt"
	"sort"
	"strings"
	"testing"

	"cel.dev/cel-go/cel"
	"cel.dev/cel-go/common/ast"
	"cel.dev/cel-go/common/types"
	"cel.dev/cel-go/ext"
	proto3pb "cel.dev/expr/conformance/proto3"

	"github.com/swist/cel-go-verifier/verifier"
)

func canonicalizationEnv(t *testing.T) *cel.Env {
	t.Helper()
	intT, strT := cel.IntType, cel.StringType
	vars := []cel.EnvOption{
		cel.Container("cel.expr.conformance.proto3"),
		cel.Types(&proto3pb.TestAllTypes{}),
		ext.TwoVarComprehensions(), ext.Bindings(), cel.OptionalTypes(),
	}
	for _, d := range []struct {
		name string
		t    *cel.Type
	}{
		{"dyn_a", cel.DynType}, {"dyn_b", cel.DynType}, {"dyn_c", cel.DynType}, {"dyn_d", cel.DynType},
		{"bool_var", cel.BoolType}, {"bool_var2", cel.BoolType},
		{"int_var", intT}, {"int_var2", intT},
		{"uint_var", cel.UintType}, {"uint_var2", cel.UintType},
		{"double_var", cel.DoubleType}, {"double_var2", cel.DoubleType},
		{"string_var", strT}, {"string_var2", strT},
		{"bytes_var", cel.BytesType}, {"bytes_var2", cel.BytesType},
		{"duration_var", cel.DurationType}, {"timestamp_var", cel.TimestampType},
		{"null_var", cel.NullType},
		{"int_list", cel.ListType(intT)}, {"string_list", cel.ListType(strT)}, {"bool_list", cel.ListType(cel.BoolType)},
		{"nested_list", cel.ListType(cel.ListType(intT))}, {"opt_list", cel.ListType(cel.OptionalType(intT))},
		{"string_int_map", cel.MapType(strT, intT)}, {"int_string_map", cel.MapType(intT, strT)},
		{"nested_map", cel.MapType(strT, cel.MapType(strT, intT))},
		{"list_map", cel.ListType(cel.MapType(strT, intT))}, {"int_list_map", cel.MapType(intT, cel.ListType(intT))},
		{"msg", cel.ObjectType("cel.expr.conformance.proto3.TestAllTypes")},
		{"msg2", cel.ObjectType("cel.expr.conformance.proto3.TestAllTypes")},
	} {
		vars = append(vars, cel.Variable(d.name, d.t))
	}
	env, err := cel.NewEnv(vars...)
	if err != nil {
		t.Fatal(err)
	}
	return env
}

// treeString prints an expression without ids. Identifiers resolved to
// qualified names (by the checker) print as those names.
func treeString(a *ast.AST, e ast.Expr) string {
	var b strings.Builder
	var walk func(e ast.Expr)
	walk = func(e ast.Expr) {
		if r, ok := a.ReferenceMap()[e.ID()]; ok && r != nil && r.Name != "" && len(r.OverloadIDs) == 0 && r.Value == nil {
			b.WriteString(r.Name)
			return
		}
		switch e.Kind() {
		case ast.LiteralKind:
			v := e.AsLiteral()
			switch v := v.(type) {
			case types.String:
				fmt.Fprintf(&b, "%q", string(v))
			case types.Bytes:
				fmt.Fprintf(&b, "b%q", []byte(v))
			case types.Uint:
				fmt.Fprintf(&b, "%du", uint64(v))
			case types.Double:
				fmt.Fprintf(&b, "%gd", float64(v))
			default:
				fmt.Fprint(&b, v.Value())
			}
		case ast.IdentKind:
			b.WriteString(e.AsIdent())
		case ast.SelectKind:
			s := e.AsSelect()
			if s.IsTestOnly() {
				b.WriteString("has(")
			}
			walk(s.Operand())
			b.WriteString("." + s.FieldName())
			if s.IsTestOnly() {
				b.WriteString(")")
			}
		case ast.CallKind:
			c := e.AsCall()
			if fn := c.FunctionName(); fn == "_&&_" || fn == "_||_" {
				// Associative chains print flat, whatever their nesting.
				b.WriteString("(" + fn)
				var flat func(e ast.Expr)
				flat = func(e ast.Expr) {
					if e.Kind() == ast.CallKind && e.AsCall().FunctionName() == fn {
						for _, arg := range e.AsCall().Args() {
							flat(arg)
						}
						return
					}
					b.WriteString(" ")
					walk(e)
				}
				flat(e)
				b.WriteString(")")
				return
			}
			b.WriteString("(" + c.FunctionName())
			if c.IsMemberFunction() {
				b.WriteString(" @")
				walk(c.Target())
			}
			for _, arg := range c.Args() {
				b.WriteString(" ")
				walk(arg)
			}
			b.WriteString(")")
		case ast.ListKind:
			l := e.AsList()
			b.WriteString("[")
			for i, el := range l.Elements() {
				if i > 0 {
					b.WriteString(", ")
				}
				if l.IsOptional(int32(i)) {
					b.WriteString("?")
				}
				walk(el)
			}
			b.WriteString("]")
		case ast.MapKind:
			b.WriteString("{")
			for i, en := range e.AsMap().Entries() {
				if i > 0 {
					b.WriteString(", ")
				}
				me := en.AsMapEntry()
				if me.IsOptional() {
					b.WriteString("?")
				}
				walk(me.Key())
				b.WriteString(": ")
				walk(me.Value())
			}
			b.WriteString("}")
		case ast.StructKind:
			s := e.AsStruct()
			name := s.TypeName()
			if r, ok := a.ReferenceMap()[e.ID()]; ok && r != nil && r.Name != "" {
				name = r.Name
			}
			b.WriteString(strings.TrimPrefix(name, "cel.expr.conformance.proto3.") + "{")
			for i, f := range s.Fields() {
				if i > 0 {
					b.WriteString(", ")
				}
				fe := f.AsStructField()
				if fe.IsOptional() {
					b.WriteString("?")
				}
				b.WriteString(fe.Name() + ": ")
				walk(fe.Value())
			}
			b.WriteString("}")
		case ast.ComprehensionKind:
			c := e.AsComprehension()
			fmt.Fprintf(&b, "(comprehension %s %s %s ", c.IterVar(), c.IterVar2(), c.AccuVar())
			for i, part := range []ast.Expr{c.IterRange(), c.AccuInit(), c.LoopCondition(), c.LoopStep(), c.Result()} {
				if i > 0 {
					b.WriteString(" ")
				}
				walk(part)
			}
			b.WriteString(")")
		}
	}
	walk(e)
	return b.String()
}

// nestedStaleMacros are cases where a rewritten comprehension nested in
// another prints as its stale predicate in cel-java's expected text (see
// below): here the inner !int_list.exists(i, e, e == v) becomes
// int_list.all(i, e, e != v), which cel-java prints as `v != e`. The check is
// that the canonical tree has the inner all() with that predicate.
var nestedStaleMacros = map[string][]string{
	"DE_MORGAN_2VAR_NESTED_COMPREHENSIONS": {
		"(comprehension k v @result string_int_map false",
		"(_==_ k \"foo\")",
		"(comprehension i e @result int_list true (@not_strictly_false @result) (_&&_ @result (_!=_ v e)) @result)",
	},
}

func TestCanonicalizationOptimizer(t *testing.T) {
	env := canonicalizationEnv(t)
	var failures []string
	for _, tc := range testCases(t, "CanonicalizationOptimizerTest.CanonicalizationTestCase") {
		name, input, expected := tc["name"].(string), tc["input"].(string), tc["expected"].(string)
		t.Run(name, func(t *testing.T) {
			a, iss := env.Compile(input)
			if iss.Err() != nil {
				t.Fatalf("compile %q: %v", input, iss.Err())
			}
			got, err := verifier.Canonicalize(env, a)
			if err != nil {
				t.Fatalf("canonicalize: %v", err)
			}
			g := treeString(got.NativeRep(), got.NativeRep().Expr())
			if parts, ok := nestedStaleMacros[name]; ok {
				for _, p := range parts {
					if !strings.Contains(g, p) {
						t.Errorf("canonicalize(%s) = %s, want it to contain %s", input, g, p)
					}
				}
				return
			}
			root := got.NativeRep().Expr()
			plain, iss := env.Compile(expected)
			if root.Kind() == ast.ComprehensionKind && (iss.Err() != nil || plain.NativeRep().Expr().Kind() != ast.ComprehensionKind) {
				// cel-java's expected text for a rewritten macro (e.g. De Morgan on
				// exists/all) is the unparse of a stale macro call, which shows only
				// the predicate. cel-java's canonical AST keeps the comprehension, as
				// its own evaluation tests of these rewrites show; compare the
				// predicate in the comprehension's scope.
				c := root.AsComprehension()
				scope := []cel.EnvOption{cel.Variable(c.IterVar(), cel.DynType)}
				if c.IterVar2() != "" {
					scope = append(scope, cel.Variable(c.IterVar2(), cel.DynType))
				}
				inner, err := env.Extend(scope...)
				if err != nil {
					t.Fatal(err)
				}
				want, iss := inner.Compile(expected)
				if iss.Err() != nil {
					t.Fatalf("compile expected %q: %v", expected, iss.Err())
				}
				// The predicate is the second operand of the step's @result && P or @result || P.
				step := c.LoopStep()
				pred := ""
				if step.Kind() == ast.CallKind && len(step.AsCall().Args()) == 2 {
					pred = treeString(got.NativeRep(), step.AsCall().Args()[1])
				}
				if w := treeString(want.NativeRep(), want.NativeRep().Expr()); pred != w {
					failures = append(failures, name)
					t.Errorf("canonicalize(%s)\n got: %s\nwant a comprehension of: %s", input, g, w)
				}
				return
			}
			if iss.Err() != nil {
				t.Fatalf("compile expected %q: %v", expected, iss.Err())
			}
			w := treeString(plain.NativeRep(), plain.NativeRep().Expr())
			if g != w {
				failures = append(failures, name)
				t.Errorf("canonicalize(%s)\n got: %s\nwant: %s (%s)", input, g, w, expected)
			}
		})
	}
	sort.Strings(failures)
	if len(failures) > 0 {
		t.Logf("%d mismatches: %v", len(failures), failures)
	}
}

func TestCanonicalizationPreservesSemantics(t *testing.T) {
	env := canonicalizationEnv(t)
	for _, tc := range []struct {
		expr string
		want bool
	}{
		{"!int_list.all(e, e == 1)", true},
		{"!int_list.exists(e, e == 1)", false},
		{"!int_list.all(e, !(e == 1))", true},
		{"!int_list.exists(e, !(e == 1))", false},
	} {
		a, iss := env.Compile(tc.expr)
		if iss.Err() != nil {
			t.Fatal(iss.Err())
		}
		c, err := verifier.Canonicalize(env, a)
		if err != nil {
			t.Fatal(err)
		}
		prg, err := env.Program(c)
		if err != nil {
			t.Fatal(err)
		}
		out, _, err := prg.Eval(map[string]any{"int_list": []int64{1, 2}})
		if err != nil {
			t.Fatal(err)
		}
		if out != types.Bool(tc.want) {
			t.Errorf("%s: got %v, want %v", tc.expr, out, tc.want)
		}
	}
}
