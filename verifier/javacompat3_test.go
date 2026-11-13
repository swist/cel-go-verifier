package verifier_test

import (
	"regexp"
	"strconv"
	"strings"
	"testing"
	"time"

	"cel.dev/cel-go/cel"
	"cel.dev/cel-go/common"
	"cel.dev/cel-go/common/ast"
	"cel.dev/cel-go/common/operators"
	"cel.dev/cel-go/common/types"
	"cel.dev/cel-go/ext"
	"cel.dev/cel-go/parser"

	"github.com/swist/cel-go-verifier/smt"
	"github.com/swist/cel-go-verifier/verifier"
)

var unsafeGoldenChars = regexp.MustCompile(`[^A-Za-z0-9_.\[\]=,-]`)

// goldenParam names the golden of a test parameterized by a string, as the javaref dump does.
func goldenParam(method, param string) string {
	name := "CelVerifierZ3ImplTest." + method + "[" + param + "]"
	return strings.TrimPrefix(unsafeGoldenChars.ReplaceAllString(name, "_"), "CelVerifierZ3ImplTest.")
}

func extendEnv(t testing.TB, base *cel.Env, opts ...cel.EnvOption) *cel.Env {
	t.Helper()
	env, err := base.Extend(opts...)
	if err != nil {
		t.Fatal(err)
	}
	return env
}

func newEnv(t testing.TB, opts ...cel.EnvOption) *cel.Env {
	t.Helper()
	env, err := cel.NewEnv(append([]cel.EnvOption{cel.CrossTypeNumericComparisons(true)}, opts...)...)
	if err != nil {
		t.Fatal(err)
	}
	return env
}

// verifierFor creates a recording verifier for env, without the test environment's message types,
// like CelVerifierFactory.newVerifier(cel) for a cel without message types.
func (g *goldenRun) verifierFor(env *cel.Env, opts ...verifier.Option) *verifier.Verifier {
	opts = append([]verifier.Option{verifier.Recorder(g.rec.Factory()), verifier.Backend(testBackend())}, opts...)
	v, err := verifier.New(env, opts...)
	if err != nil {
		g.t.Fatal(err)
	}
	return v
}

func fn(name string, overloads ...cel.FunctionOpt) cel.EnvOption {
	return cel.Function(name, overloads...)
}

func requestFnEnv(t testing.TB) *cel.Env {
	return extendEnv(t, javaTestEnv(t), fn("request", cel.Overload("request_overload", nil, cel.DynType)))
}

func TestIsSatisfiableMaskedByBmcNestedInconclusive(t *testing.T) {
	single(t, "isSatisfiable_maskedByBmcNested_inconclusive", func(t *testing.T, g *goldenRun) {
		r := must(t)(g.verifier(verifier.ComprehensionUnrollLimit(3)).IsSatisfiable(compile(t, javaTestEnv(t),
			"nested_list == [[1, 2, 3, 4, 5, 6]] ? nested_list.exists(row, row.exists(x, x == 42)) : false")))
		expectStatus(t, r, verifier.Inconclusive)
	})
}

func TestIsSatisfiableComprehensionZeroUnrollLimitInconclusive(t *testing.T) {
	single(t, "isSatisfiable_comprehensionZeroUnrollLimit_inconclusive", func(t *testing.T, g *goldenRun) {
		r := must(t)(g.verifier(verifier.ComprehensionUnrollLimit(0)).IsSatisfiable(compile(t, javaTestEnv(t), "int_list == [1] ? int_list.exists(x, x == 1) : false")))
		expectStatus(t, r, verifier.Inconclusive)
	})
}

func TestIsSatisfiableTimeoutThrowsException(t *testing.T) {
	requireZ3(t)
	g := newGoldenRun(t, z3+"isSatisfiable_timeout_throwsException")
	v := g.verifierFor(newEnv(t), verifier.Timeout(time.Millisecond))
	_, err := v.IsSatisfiable(compile(t, javaTestEnv(t), "int_list.all(x, int_list.all(y, int_list.all(z, x + y + z > 0)))"))
	if err == nil || !strings.Contains(err.Error(), "timed out") {
		t.Errorf("err = %v, want a timeout", err)
	}
}

func TestIsAlwaysTrueWithUnknownIdentifierEvaluatesToUnknown(t *testing.T) {
	for _, e := range []string{"x == x", "[x] == [x]", "{1: x} == {1: x}", "size(int_list) == 1 ? int_list.all(i, x == x) : true"} {
		e := e
		t.Run(e, func(t *testing.T) {
			single(t, goldenParam("isAlwaysTrue_withUnknownIdentifier_evaluatesToUnknown", e), func(t *testing.T, g *goldenRun) {
				r := must(t)(g.verifier(verifier.UnknownIdentifiers("x")).IsAlwaysTrue(compile(t, javaTestEnv(t), e)))
				expectStatus(t, r, verifier.Violated)
				contains(t, r.Message(), "x = Unknown")
				if r.Witness.Variables["x"].Value != nil {
					t.Errorf("x has a runtime value")
				}
			})
		})
	}
}

func TestIsAlwaysTrueApproximateBesideUnknownInconclusive(t *testing.T) {
	runTable(t, "ApproximateBesideUnknownTestCase", "isAlwaysTrue_approximateBesideUnknown_inconclusive", func(t *testing.T, g *goldenRun, c map[string]any) {
		r := must(t)(g.verifier(verifier.UnknownIdentifiers("unknown_var")).IsAlwaysTrue(compile(t, javaTestEnv(t), str(c, "expr"))))
		expectStatus(t, r, verifier.Inconclusive)
		contains(t, r.Message(), "doesn't model exactly: "+str(c, "expectedSources")+".")
	})
}

func TestIsAlwaysTrueDynamicComprehensionNonBoolYieldsError(t *testing.T) {
	single(t, "isAlwaysTrue_dynamicComprehensionNonBoolYieldsError", func(t *testing.T, g *goldenRun) {
		r := must(t)(g.verifier(verifier.ComprehensionUnrollLimit(1)).IsAlwaysTrue(compile(t, javaTestEnv(t),
			"dyn_list == [{'not_a_bool': 123}] ? !(dyn_list.all(x, x.not_a_bool) == true || dyn_list.all(x, x.not_a_bool) == false) : true")))
		expectStatus(t, r, verifier.Violated)
		if !regexp.MustCompile(`^Condition is not always true\. Counterexample input:\n  dyn_list = \[\{"not_a_bool": 123(u|\.0)?\}\]$`).MatchString(r.Message()) {
			t.Errorf("message = %q", r.Message())
		}
	})
}

func TestIsAlwaysTrueComprehensionUnrollLimits(t *testing.T) {
	for _, tc := range []struct {
		method, expr string
		limit        int
		want         verifier.Status
	}{
		{"isAlwaysTrue_comprehensionExceedsMaxIterations_returnsUnknown", "int_list == [1, 2, 3] ? int_list.all(x, x > 0) : true", 2, verifier.Inconclusive},
		{"isAlwaysTrue_comprehensionZeroUnrollLimit_emptyList", "int_list == [] ? int_list.all(x, x > 0) : true", 0, verifier.Verified},
	} {
		tc := tc
		t.Run(tc.method, func(t *testing.T) {
			single(t, tc.method, func(t *testing.T, g *goldenRun) {
				r := must(t)(g.verifier(verifier.ComprehensionUnrollLimit(tc.limit)).IsAlwaysTrue(compile(t, javaTestEnv(t), tc.expr)))
				expectStatus(t, r, tc.want)
			})
		})
	}
}

func TestIsAlwaysTrueUnpopulatedTypesFails(t *testing.T) {
	requireZ3(t)
	env := javaTestEnv(t)
	parsed, iss := env.Parse("1 == 1")
	if iss.Err() != nil {
		t.Fatal(iss.Err())
	}
	v, err := verifier.New(env, verifier.Backend(testBackend()))
	if err != nil {
		t.Fatal(err)
	}
	if _, err := v.IsAlwaysTrue(parsed); err == nil || !strings.Contains(err.Error(), "AST must be type-checked") {
		t.Errorf("err = %v", err)
	}
}

func TestIsAlwaysTrueStrictCustomFunctionErrorPropagates(t *testing.T) {
	single(t, "isAlwaysTrue_strictCustomFunction_errorPropagates", func(t *testing.T, g *goldenRun) {
		env := newEnv(t, cel.Container("cel.expr.conformance.proto3"),
			fn("custom_func", cel.Overload("custom_func_overload", []*cel.Type{cel.IntType}, cel.IntType)))
		r := must(t)(g.verifier().IsAlwaysTrue(compile(t, env, "custom_func(1 / 0) == 5 || !(custom_func(1 / 0) == 5)")))
		expectStatus(t, r, verifier.Violated)
		if want := "Condition is not always true. (The expression fails unconditionally, regardless of input state)"; r.Message() != want {
			t.Errorf("message = %q", r.Message())
		}
	})
}

func TestVerifyEquivalenceUnknownPrecedenceOverError(t *testing.T) {
	single(t, "verifyEquivalence_unknownPrecedenceOverError", func(t *testing.T, g *goldenRun) {
		env := newEnv(t, cel.Variable("unknown_var", cel.DynType),
			fn("custom_func", cel.Overload("custom_func_overload", []*cel.Type{cel.IntType, cel.DynType}, cel.IntType)))
		v := g.verifierFor(env, verifier.UnknownIdentifiers("unknown_var"))
		r := must(t)(v.VerifyEquivalence(compile(t, env, "custom_func(1 / 0, unknown_var)"), compile(t, env, "1 / 0")))
		expectStatus(t, r, verifier.Violated)
	})
}

func TestVerifyEquivalenceWithUnknownIdentifiersInconclusive(t *testing.T) {
	runTable(t, "UnknownIdentifierEquivalenceTestCase", "verifyEquivalence_withUnknownIdentifiers_inconclusive", func(t *testing.T, g *goldenRun, c map[string]any) {
		env := javaTestEnv(t)
		v := g.verifier(verifier.UnknownIdentifiers("a", "x", "unknown_var"))
		r := must(t)(v.VerifyEquivalence(compile(t, env, str(c, "exprA")), compile(t, env, str(c, "exprB"))))
		expectStatus(t, r, verifier.Inconclusive)
	})
}

func TestVerifyEquivalenceFreeVariableIndicesDeduplicated(t *testing.T) {
	single(t, "verifyEquivalence_freeVariableIndicesDeduplicated", func(t *testing.T, g *goldenRun) {
		env := javaTestEnv(t)
		r := must(t)(g.verifier().VerifyEquivalence(
			compile(t, env, "x == y && y == port ? dyn_list.all(e, x == x) : false"),
			compile(t, env, "x == y && y == port ? dyn_list.all(e, y == port) : false")))
		expectStatus(t, r, verifier.Inconclusive)
	})
}

func TestIsSatisfiableApproximateIterRangeInMapInconclusive(t *testing.T) {
	single(t, "isSatisfiable_approximateIterRangeInMap_inconclusive", func(t *testing.T, g *goldenRun) {
		env := newEnv(t, cel.Container("cel.expr.conformance.proto3"),
			fn("approx_list", cel.Overload("approx_list_overload", []*cel.Type{cel.IntType}, cel.ListType(cel.IntType))))
		r := must(t)(g.verifier().IsSatisfiable(compile(t, env, "approx_list(1).map(x, x * 2) == []")))
		expectStatus(t, r, verifier.Inconclusive)
	})
}

func TestIsSatisfiableMapWithUnusedApproximateIterationVerified(t *testing.T) {
	single(t, "isSatisfiable_mapWithUnusedApproximateIteration_verified", func(t *testing.T, g *goldenRun) {
		env := newEnv(t, cel.Variable("y", cel.ListType(cel.IntType)),
			fn("approx_func", cel.Overload("approx_func_overload", []*cel.Type{cel.IntType}, cel.IntType)))
		r := must(t)(g.verifier().IsSatisfiable(compile(t, env, "y == [] && y.map(x, approx_func(1)) == y")))
		expectStatus(t, r, verifier.Verified)
	})
}

func TestUnconditionalErrorFailsVerification(t *testing.T) {
	runTable(t, "UnconditionalErrorTestCase", "isAlwaysTrue_unconditionalError_failsVerification", func(t *testing.T, g *goldenRun, c map[string]any) {
		r := must(t)(g.verifier().IsAlwaysTrue(compile(t, javaTestEnv(t), str(c, "expr"))))
		expectStatus(t, r, verifier.Violated)
		if want := "Condition is not always true. (The expression fails unconditionally, regardless of input state)"; r.Message() != want {
			t.Errorf("message = %q", r.Message())
		}
	})
	runTable(t, "UnconditionalErrorTestCase", "verifyEquivalence_unconditionalError_failsVerification", func(t *testing.T, g *goldenRun, c map[string]any) {
		env := javaTestEnv(t)
		r := must(t)(g.verifier().VerifyEquivalence(compile(t, env, str(c, "expr")), compile(t, env, "true")))
		expectStatus(t, r, verifier.Violated)
		if want := "Equivalence violation detected. (The expression fails unconditionally, regardless of input state)"; r.Message() != want {
			t.Errorf("message = %q", r.Message())
		}
	})
}

func TestVerifyEquivalenceDynamicMapEqualityEnforcesExtensionality(t *testing.T) {
	single(t, "verifyEquivalence_dynamicMapEquality_enforcesExtensionalityOnPresentKeys", func(t *testing.T, g *goldenRun) {
		env := javaTestEnv(t)
		r := must(t)(g.verifier().VerifyEquivalence(compile(t, env, "string_int_map == {'a': 1}"), compile(t, env, "true")))
		expectStatus(t, r, verifier.Violated)
		contains(t, r.Message(), "string_int_map =")
		notContains(t, r.Message(), "string_int_map = {'a': 1}")
	})
}

func TestIsAlwaysTrueMalformedAstFails(t *testing.T) {
	requireZ3(t)
	env := javaTestEnv(t)
	valid := compile(t, env, "1 < 2")
	f := ast.NewExprFactory()
	for name, tc := range map[string]struct {
		op   string
		args []ast.Expr
		want string
	}{
		"LOGICAL_AND": {operators.LogicalAnd, []ast.Expr{f.NewLiteral(2, types.True)}, "expects at least 2 arguments, got 1"},
		"NEGATE":      {operators.Negate, nil, "expects 1 argument, got 0"},
		"CONDITIONAL": {operators.Conditional, []ast.Expr{f.NewLiteral(2, types.True), f.NewLiteral(3, types.Int(1))}, "expects 3 arguments, got 2"},
		"LESS":        {operators.Less, []ast.Expr{f.NewLiteral(2, types.Int(1))}, "expects 2 arguments, got 1"},
	} {
		t.Run(name, func(t *testing.T) {
			native := valid.NativeRep()
			malformed := ast.NewCheckedAST(ast.NewAST(f.NewCall(1, tc.op, tc.args...), native.SourceInfo()), native.TypeMap(), native.ReferenceMap())
			pb, err := ast.ToProto(malformed)
			if err != nil {
				t.Fatal(err)
			}
			v, err := verifier.New(env, verifier.Backend(testBackend()))
			if err != nil {
				t.Fatal(err)
			}
			if _, err := v.IsAlwaysTrue(cel.CheckedExprToAst(pb)); err == nil || !strings.Contains(err.Error(), tc.want) {
				t.Errorf("err = %v, want %q", err, tc.want)
			}
		})
	}
}

// constantFold folds constants like cel-java's ConstantFoldingOptimizer.
func constantFold(t *testing.T, env *cel.Env, a *cel.Ast) *cel.Ast {
	t.Helper()
	folder, err := cel.NewConstantFoldingOptimizer()
	if err != nil {
		t.Fatal(err)
	}
	opt, err := cel.NewStaticOptimizer(folder)
	if err != nil {
		t.Fatal(err)
	}
	out, iss := opt.Optimize(env, a)
	if iss.Err() != nil {
		t.Fatal(iss.Err())
	}
	return out
}

func TestVerifyEquivalenceInfinityConstantsNotEquivalent(t *testing.T) {
	single(t, "verifyEquivalence_infinityConstants_notEquivalent", func(t *testing.T, g *goldenRun) {
		env := javaTestEnv(t)
		r := must(t)(g.verifier().VerifyEquivalence(
			constantFold(t, env, compile(t, env, "d == double('Infinity')")),
			constantFold(t, env, compile(t, env, "d == double('-Infinity')"))))
		expectStatus(t, r, verifier.Violated)
	})
}

func TestIsAlwaysTrueNanAndInfinityConstants(t *testing.T) {
	for _, e := range []string{"request.single_double == double('NaN')", "request.single_double == double('Infinity')", "request.single_double == double('-Infinity')"} {
		e := e
		t.Run(e, func(t *testing.T) {
			single(t, goldenParam("isAlwaysTrue_nanAndInfinityConstants_isFalse", e), func(t *testing.T, g *goldenRun) {
				env := javaTestEnv(t)
				expectStatus(t, must(t)(g.verifier().IsAlwaysTrue(constantFold(t, env, compile(t, env, e)))), verifier.Violated)
			})
		})
	}
	for _, e := range []string{"double('Infinity') == double('Infinity')", "double('-Infinity') == double('-Infinity')", "double('Infinity') > double('-Infinity')", "double('NaN') != double('NaN')"} {
		e := e
		t.Run(e, func(t *testing.T) {
			single(t, goldenParam("isAlwaysTrue_nanAndInfinityConstants_tautology", e), func(t *testing.T, g *goldenRun) {
				env := javaTestEnv(t)
				expectStatus(t, must(t)(g.verifier().IsAlwaysTrue(constantFold(t, env, compile(t, env, e)))), verifier.Verified)
			})
		})
	}
}

func TestIsAlwaysTrueDynValuesComparedWithIntConstantVerified(t *testing.T) {
	for _, e := range []string{
		"dyn_map == {'a': 1, 'b': 2} ? dyn_map.all(k, v, k == 'a' || v > 1) : true",
		"dyn_map == {'a': 1, 'b': 2} ? dyn_map.all(k, v, k == 'b' || v < 2) : true",
	} {
		e := e
		t.Run(e, func(t *testing.T) {
			single(t, goldenParam("isAlwaysTrue_dynValuesComparedWithIntConstant_verified", e), func(t *testing.T, g *goldenRun) {
				r := must(t)(g.verifier(verifier.Timeout(5 * time.Second)).IsAlwaysTrue(compile(t, javaTestEnv(t), e)))
				expectStatus(t, r, verifier.Verified)
			})
		})
	}
}

func TestIsAlwaysTrueDynamicMapComprehensionNestedEqualityViolated(t *testing.T) {
	single(t, "isAlwaysTrue_dynamicMapComprehensionNestedEquality_violated", func(t *testing.T, g *goldenRun) {
		r := must(t)(g.verifier(verifier.Timeout(20 * time.Second)).IsAlwaysTrue(compile(t, javaTestEnv(t),
			"cel.bind(r, request, r.l == [[1], [2], [3], [4], [5]] && r.m == {1: [1], 2: [2], 3: [3]} ? r.l.all(x, r.m.exists(k, r.m[k] == x)) : true)")))
		expectStatus(t, r, verifier.Violated)
		contains(t, r.Message(), "request = ")
	})
}

func TestIsAlwaysTrueInconclusiveContainsPotentialCounterexample(t *testing.T) {
	single(t, "isAlwaysTrue_inconclusive_containsPotentialCounterexample", func(t *testing.T, g *goldenRun) {
		r := must(t)(g.verifier().IsAlwaysTrue(compile(t, javaTestEnv(t), "request.matches('^[a-z]+$') == true")))
		expectStatus(t, r, verifier.Inconclusive)
		matches(t, r.Message(), `Potential counterexample input:\n\s*request = .*`)
	})
}

const inconclusiveDivergence = "Inconclusive: a divergence may exist, but it depends on what the verifier doesn't model exactly: "

func TestVerifyEquivalenceApproximationSources(t *testing.T) {
	for _, tc := range []struct {
		method, a, b, sources string
		opts                  []verifier.Option
	}{
		{"verifyEquivalence_dynComprehensionRange_listedAsApproximationSource", "dyn_var.all(e, e > 0)", "dyn_var.all(e, e < 0)", "comprehensions over `dyn` values", nil},
		{"verifyEquivalence_unknownResults_listedAsApproximationSource", "unknown_var * 1", "unknown_var + 0", "unknown results, which are compared only by their origin", []verifier.Option{verifier.UnknownIdentifiers("unknown_var")}},
	} {
		tc := tc
		t.Run(tc.method, func(t *testing.T) {
			single(t, tc.method, func(t *testing.T, g *goldenRun) {
				env := javaTestEnv(t)
				r := must(t)(g.verifier(tc.opts...).VerifyEquivalence(compile(t, env, tc.a), compile(t, env, tc.b)))
				if want := inconclusiveDivergence + tc.sources + "."; r.Reason != want {
					t.Errorf("reason = %q, want %q", r.Reason, want)
				}
			})
		})
	}
}

func TestVerifyEquivalenceSingles(t *testing.T) {
	for _, tc := range []struct {
		method, a, b string
		want         verifier.Status
		contains     []string
		matches      []string
	}{
		{"verifyEquivalence_violation_hasCounterexampleMessage", "x > y", "x > 5", verifier.Violated,
			[]string{"Equivalence violation detected. Counterexample input:"}, []string{` {2}x = -?\d+`, ` {2}y = -?\d+`}},
		{"verifyEquivalence_divergesOnTernaryErrorSemantics", "true", "(1 / 0 == 1) ? true : true", verifier.Violated, nil, nil},
		{"verifyEquivalence_dynamicIndexingWithExplicitMap_hydratesMap", `string_int_list_map == {"a": [1, 2], "b": [3, 4]}`, `string_int_list_map == {"a": [1, 2], "b": [3, 5]}`, verifier.Violated,
			[]string{"string_int_list_map = {", `"a": [1, 2]`}, []string{`"b": \[3, [45]]`}},
		{"verifyEquivalence_logicalAndShortCircuitError_isVerified", "false && (1 / 0 == 0)", "false", verifier.Verified, nil, nil},
		{"verifyEquivalence_logicalOrShortCircuitUnknown_isVerified", "true || unknown_var", "true", verifier.Verified, nil, nil},
		{"verifyEquivalence_deepListExtensionality_isVerified", "[[[[1]]]] == [[[[1]]]]", "true", verifier.Verified, nil, nil},
		{"verifyEquivalence_stringConcatenationExplosion_isVerified", `("a" + "b" + "c" + "d" + "e") == "abcde"`, "true", verifier.Verified, nil, nil},
		{"verifyEquivalence_divergesOnShortCircuitingErrors", `true || (role == "admin" && 1 / 0 == 1)`, `(role == "admin" && 1 / 0 == 1) || true`, verifier.Verified, nil, nil},
		{"verifyEquivalence_distinctErrorEquivalence_failsVerification", "5u + 5u == 10u", `role + role == "abc"`, verifier.Violated, nil, nil},
	} {
		tc := tc
		t.Run(tc.method, func(t *testing.T) {
			single(t, tc.method, func(t *testing.T, g *goldenRun) {
				env := javaTestEnv(t)
				r := must(t)(g.verifier().VerifyEquivalence(compile(t, env, tc.a), compile(t, env, tc.b)))
				expectStatus(t, r, tc.want)
				for _, c := range tc.contains {
					contains(t, r.Message(), c)
				}
				for _, m := range tc.matches {
					matches(t, r.Message(), m)
				}
			})
		})
	}
}

func TestVerifyEquivalenceCounterexampleFormat(t *testing.T) {
	runTable(t, "CounterexampleFormatTestCase", "verifyEquivalence_counterexampleFormat", func(t *testing.T, g *goldenRun, c map[string]any) {
		env := javaTestEnv(t)
		r := must(t)(g.verifier().VerifyEquivalence(compile(t, env, str(c, "exprA")), compile(t, env, str(c, "exprB"))))
		expectStatus(t, r, verifier.Violated)
		ok := false
		for _, f := range strs(c, "expectedFragments") {
			if regexp.MustCompile(`(?s)^.*Equivalence violation detected\. Counterexample input:\n {2}` + f + `.*$`).MatchString(r.Message()) {
				ok = true
			}
		}
		if !ok {
			t.Errorf("message %q matches none of %q", r.Message(), strs(c, "expectedFragments"))
		}
	})
}

func TestVerifyEquivalenceStructCounterexampleFormat(t *testing.T) {
	single(t, "verifyEquivalence_structCounterexampleFormat", func(t *testing.T, g *goldenRun) {
		env := javaTestEnv(t)
		r := must(t)(g.verifier().VerifyEquivalence(compile(t, env, "test_all_types == TestAllTypes{single_int32: 1}"), compile(t, env, "test_all_types == TestAllTypes{single_int32: 2}")))
		expectStatus(t, r, verifier.Violated)
		prefix := "Equivalence violation detected. Counterexample input:\n  test_all_types = cel.expr.conformance.proto3.TestAllTypes{single_int32: "
		if r.Message() != prefix+"1}" && r.Message() != prefix+"2}" {
			t.Errorf("message = %q", r.Message())
		}
	})
}

func TestIsAlwaysTrueOperationErrorCounterexampleFormat(t *testing.T) {
	single(t, "isAlwaysTrue_operationError_counterexampleFormat", func(t *testing.T, g *goldenRun) {
		r := must(t)(g.verifier().IsAlwaysTrue(compile(t, javaTestEnv(t), "x / x == x / x")))
		expectStatus(t, r, verifier.Violated)
		contains(t, r.Message(), "x = 0")
	})
}

func TestUninterpretedFunctionCalls(t *testing.T) {
	boolFnEnv := func(t testing.TB) *cel.Env {
		return extendEnv(t, javaTestEnv(t), fn("bool_func", cel.Overload("bool_func_overload", nil, cel.BoolType)))
	}
	symbolsEnv := func(t testing.TB) *cel.Env {
		return extendEnv(t, javaTestEnv(t),
			cel.Variable("string_list", cel.ListType(cel.StringType)),
			fn("fx", cel.Overload("fx_global", []*cel.Type{cel.StringType, cel.StringType}, cel.BoolType),
				cel.MemberOverload("fx_member", []*cel.Type{cel.StringType, cel.StringType}, cel.BoolType)),
			fn("f", cel.Overload("f_list_int", []*cel.Type{cel.ListType(cel.IntType)}, cel.IntType),
				cel.Overload("f_list_string", []*cel.Type{cel.ListType(cel.StringType)}, cel.IntType)))
	}
	for _, tc := range []struct {
		golden, expr string
		env          func(testing.TB) *cel.Env
		want         verifier.Status
		contains     string
	}{
		{"isAlwaysTrue_dynamicFunction_inconclusive", "request() == request()", requestFnEnv, verifier.Inconclusive, "doesn't model exactly: calls to `request`."},
		{"isAlwaysTrue_dynamicFunctionShortCircuited_violated", "x != 0 && request() == 1", requestFnEnv, verifier.Violated, "x = 0"},
		{"isAlwaysTrue_boolFunction_verified", "bool_func() == bool_func()", boolFnEnv, verifier.Verified, ""},
		{goldenParam("isAlwaysTrue_distinctFunctionSymbols_inconclusive", "fx(role, country) == role.fx(country)"), "fx(role, country) == role.fx(country)", symbolsEnv, verifier.Inconclusive, ""},
		{goldenParam("isAlwaysTrue_distinctFunctionSymbols_inconclusive", "size(int_list) == 0 && size(string_list) == 0 ? f(int_list) == f(string_list) : true"),
			"size(int_list) == 0 && size(string_list) == 0 ? f(int_list) == f(string_list) : true", symbolsEnv, verifier.Inconclusive, ""},
		{"isAlwaysTrue_zeroArityFunctionAndSameNamedVariable_inconclusive", "g() == g", func(t testing.TB) *cel.Env {
			return extendEnv(t, javaTestEnv(t), cel.Variable("g", cel.IntType), fn("g", cel.Overload("g_zero", nil, cel.IntType)))
		}, verifier.Inconclusive, ""},
	} {
		tc := tc
		t.Run(tc.golden, func(t *testing.T) {
			single(t, tc.golden, func(t *testing.T, g *goldenRun) {
				r := must(t)(g.verifier().IsAlwaysTrue(compile(t, tc.env(t), tc.expr)))
				expectStatus(t, r, tc.want)
				if tc.contains != "" {
					contains(t, r.Message(), tc.contains)
				}
			})
		})
	}
	t.Run("verifyEquivalence_identicalFunctionCalls_equivalent", func(t *testing.T) {
		single(t, "verifyEquivalence_identicalFunctionCalls_equivalent", func(t *testing.T, g *goldenRun) {
			env := requestFnEnv(t)
			r := must(t)(g.verifier().VerifyEquivalence(compile(t, env, "request()"), compile(t, env, "request()")))
			expectStatus(t, r, verifier.Verified)
		})
	})
	t.Run("isSatisfiable_customOperatorOverload_inconclusive", func(t *testing.T) {
		single(t, "isSatisfiable_customOperatorOverload_inconclusive", func(t *testing.T, g *goldenRun) {
			env := extendEnv(t, javaTestEnv(t), fn(operators.Less,
				cel.Overload("less_list_int", []*cel.Type{cel.ListType(cel.IntType), cel.ListType(cel.IntType)}, cel.BoolType)))
			r := must(t)(g.verifier().IsSatisfiable(compile(t, env, "!(int_list < int_list_2)")))
			expectStatus(t, r, verifier.Inconclusive)
		})
	})
}

func TestTimeoutInvalidDurationFails(t *testing.T) {
	for _, d := range []time.Duration{0, -time.Second} {
		if _, err := verifier.New(javaTestEnv(t), verifier.Timeout(d)); err == nil || !strings.Contains(err.Error(), "timeout must be strictly positive") {
			t.Errorf("Timeout(%v): err = %v", d, err)
		}
	}
}

func TestIsSatisfiableDivisionByZeroFailsInCelWithErrors(t *testing.T) {
	single(t, "isSatisfiable_divisionByZero_failsInCelWithErrors", func(t *testing.T, g *goldenRun) {
		expectStatus(t, must(t)(g.verifier().IsSatisfiable(compile(t, javaTestEnv(t), "1 / 0 == 5"))), verifier.Violated)
	})
}

func doublesEnv(t testing.TB) *cel.Env {
	return newEnv(t, cel.Variable("d1", cel.DoubleType), cel.Variable("d2", cel.DoubleType), cel.Variable("d3", cel.DoubleType), cel.Variable("d4", cel.DoubleType))
}

func TestTimeoutReachedFails(t *testing.T) {
	requireZ3(t)
	env := doublesEnv(t)
	t.Run("isSatisfiable", func(t *testing.T) {
		g := newGoldenRun(t, z3+"isSatisfiable_timeoutReached_throwsCelVerificationException")
		_, err := g.verifierFor(env, verifier.Timeout(time.Millisecond)).IsSatisfiable(compile(t, env,
			"d1 * d2 * d3 * d4 * d1 * d2 * d3 * d4 * d1 * d2 * d3 * d4 * d1 * d2 * d3 * d4 == 9429185123491285.0 && d1 > 1.0 && d2 > 1.0 && d3 > 1.0 && d4 > 1.0"))
		if err == nil || !regexp.MustCompile("timeout|canceled").MatchString(err.Error()) {
			t.Errorf("err = %v", err)
		}
	})
	t.Run("verifyEquivalence", func(t *testing.T) {
		g := newGoldenRun(t, z3+"verifyEquivalence_timeoutReached_throwsCelVerificationException")
		_, err := g.verifierFor(env, verifier.Timeout(time.Millisecond)).VerifyEquivalence(compile(t, env,
			"d1 * d2 * d3 * d4 * d1 * d2 * d3 * d4 == 9429185123491285.0 && d1 > 100000.0 && d2 > 100000.0 && d3 > 100000.0 && d4 > 100000.0"), compile(t, env, "false"))
		if err == nil || !regexp.MustCompile("timeout|canceled").MatchString(err.Error()) {
			t.Errorf("err = %v", err)
		}
	})
}

func decl(name string, overloads ...verifier.OverloadDecl) verifier.FunctionDecl {
	return verifier.FunctionDecl{Name: name, Overloads: overloads}
}

func ov(id string, result *types.Type, params ...*types.Type) verifier.OverloadDecl {
	return verifier.OverloadDecl{ID: id, Params: params, Result: result}
}

func TestFunctionAxioms(t *testing.T) {
	t.Run("addFunctionAxioms_iterable_addsToAxioms", func(t *testing.T) {
		single(t, "addFunctionAxioms_iterable_addsToAxioms", func(t *testing.T, g *goldenRun) {
			ax := verifier.NewFunctionAxiom(decl("dummy", ov("dummy_overload", types.IntType))).
				Overload("dummy_overload", func(c *smt.Context, ts *verifier.TypeSystem, _ func(*smt.Term), _, _ []*smt.Term) (verifier.OverloadResult, bool) {
					return verifier.OverloadResult{Value: ts.WrapInt(c.MkInt(42)), Approx: c.MkFalse()}, true
				})
			env := extendEnv(t, javaTestEnv(t), fn("dummy", cel.Overload("dummy_overload", nil, cel.IntType)))
			r := must(t)(g.verifierFor(newEnv(t), verifier.FunctionAxioms(ax)).IsAlwaysTrue(compile(t, env, "dummy() == 42")))
			expectStatus(t, r, verifier.Verified)
		})
	})
	t.Run("isAlwaysTrue_functionAxiomWithErrorArgument_bubblesUpError", func(t *testing.T) {
		single(t, "isAlwaysTrue_functionAxiomWithErrorArgument_bubblesUpError", func(t *testing.T, g *goldenRun) {
			ax := verifier.NewFunctionAxiom(decl("dummy", ov("dummy_overload", types.DynType, types.DynType))).
				Unary("dummy_overload", func(c *smt.Context, ts *verifier.TypeSystem, _ func(*smt.Term), _ *smt.Term) (*smt.Term, bool) {
					return ts.MkInt(42), true
				}, false)
			env := extendEnv(t, javaTestEnv(t), fn("dummy", cel.Overload("dummy_overload", []*cel.Type{cel.DynType}, cel.DynType)))
			r := must(t)(g.verifierFor(newEnv(t), verifier.FunctionAxioms(ax)).IsAlwaysTrue(compile(t, env, "dummy(x / x) == 42")))
			expectStatus(t, r, verifier.Violated)
			contains(t, r.Message(), "x = 0")
		})
	})
	t.Run("addFunctionAxioms_axiomHandlesNothing_fallsBackToUninterpretedFunction", func(t *testing.T) {
		single(t, "addFunctionAxioms_axiomHandlesNothing_fallsBackToUninterpretedFunction", func(t *testing.T, g *goldenRun) {
			ax := verifier.NewFunctionAxiom(decl("dummy_add", ov("dummy_add_overload", types.IntType, types.IntType, types.IntType))).
				Binary("dummy_add_overload", func(*smt.Context, *verifier.TypeSystem, func(*smt.Term), *smt.Term, *smt.Term) (*smt.Term, bool) {
					return nil, false
				})
			env := newEnv(t, fn("dummy_add", cel.Overload("dummy_add_overload", []*cel.Type{cel.IntType, cel.IntType}, cel.IntType)))
			r := must(t)(g.verifierFor(newEnv(t), verifier.FunctionAxioms(ax)).IsAlwaysTrue(compile(t, env, "dummy_add(1, 1) == 2")))
			expectStatus(t, r, verifier.Inconclusive)
		})
	})
	runTable(t, "TernaryApproxTestCase", "addFunctionAxioms_ternaryOverload_approximation_inconclusive", func(t *testing.T, g *goldenRun, c map[string]any) {
		ax := verifier.NewFunctionAxiom(decl("dummy_ternary", ov("dummy_ternary_overload", types.IntType, types.IntType, types.IntType, types.IntType))).
			Ternary("dummy_ternary_overload", func(c *smt.Context, ts *verifier.TypeSystem, _ func(*smt.Term), a, b, d *smt.Term) (*smt.Term, bool) {
				return ts.WrapInt(c.MkAdd(ts.GetInt(a), ts.GetInt(b), ts.GetInt(d))), true
			})
		env := newEnv(t,
			fn("dummy_ternary", cel.Overload("dummy_ternary_overload", []*cel.Type{cel.IntType, cel.IntType, cel.IntType}, cel.IntType)),
			fn("uninterpreted_int", cel.Overload("uninterpreted_int_overload", nil, cel.IntType)))
		r := must(t)(g.verifierFor(newEnv(t), verifier.FunctionAxioms(ax)).IsAlwaysTrue(compile(t, env, str(c, "expr"))))
		expectStatus(t, r, verifier.Inconclusive)
	})
	t.Run("addFunctionAxioms_heterogeneousArguments_checksAllTypes", func(t *testing.T) {
		single(t, "addFunctionAxioms_heterogeneousArguments_checksAllTypes", func(t *testing.T, g *goldenRun) {
			listDyn := types.NewListType(types.DynType)
			ret := func(n int64) verifier.BinaryTranslator {
				return func(c *smt.Context, ts *verifier.TypeSystem, _ func(*smt.Term), _, _ *smt.Term) (*smt.Term, bool) {
					return ts.WrapInt(c.MkInt(n)), true
				}
			}
			ax := verifier.NewFunctionAxiom(decl("dummy_func",
				ov("dummy_func_list", types.IntType, listDyn, listDyn),
				ov("dummy_func_int", types.IntType, types.IntType, listDyn))).
				Binary("dummy_func_list", ret(1)).Binary("dummy_func_int", ret(2))
			env := newEnv(t, cel.Variable("int_var", cel.IntType), fn("dummy_func",
				cel.Overload("dummy_func_list", []*cel.Type{cel.ListType(cel.DynType), cel.ListType(cel.DynType)}, cel.IntType),
				cel.Overload("dummy_func_int", []*cel.Type{cel.IntType, cel.ListType(cel.DynType)}, cel.IntType)))
			r := must(t)(g.verifierFor(newEnv(t), verifier.FunctionAxioms(ax)).IsAlwaysTrue(compile(t, env, "int_var == 1 ? dummy_func(int_var, [1]) == 2 : true")))
			expectStatus(t, r, verifier.Verified)
		})
	})
	t.Run("addFunctionAxioms_duplicateFunctionNames_throwsException", func(t *testing.T) {
		id := func(c *smt.Context, ts *verifier.TypeSystem, _ func(*smt.Term), _ *smt.Term) (*smt.Term, bool) {
			return ts.WrapInt(c.MkInt(1)), true
		}
		a1 := verifier.NewFunctionAxiom(decl("dummy_func", ov("dummy_func_int", types.IntType, types.IntType))).Unary("dummy_func_int", id, false)
		a2 := verifier.NewFunctionAxiom(decl("dummy_func", ov("dummy_func_list", types.IntType, types.NewListType(types.DynType)))).Unary("dummy_func_list", id, false)
		if _, err := verifier.New(newEnv(t), verifier.FunctionAxioms(a1, a2)); err == nil || !strings.Contains(err.Error(), "dummy_func") {
			t.Errorf("err = %v", err)
		}
	})
	t.Run("addFunctionAxioms_allPrimitiveTypes_checksAllTypes", func(t *testing.T) {
		single(t, "addFunctionAxioms_allPrimitiveTypes_checksAllTypes", func(t *testing.T, g *goldenRun) {
			msg := types.NewObjectType("test.Message")
			ax := verifier.NewFunctionAxiom(decl("dummy_all_types", ov("dummy_all_types_overload", types.BoolType,
				types.UintType, types.DoubleType, types.BoolType, types.StringType, types.BytesType, msg))).
				Overload("dummy_all_types_overload", func(c *smt.Context, ts *verifier.TypeSystem, _ func(*smt.Term), _, _ []*smt.Term) (verifier.OverloadResult, bool) {
					return verifier.OverloadResult{Value: ts.WrapBool(c.MkTrue()), Approx: c.MkFalse()}, true
				})
			env := newEnv(t,
				cel.Variable("uint_var", cel.UintType), cel.Variable("double_var", cel.DoubleType), cel.Variable("bool_var", cel.BoolType),
				cel.Variable("string_var", cel.StringType), cel.Variable("bytes_var", cel.BytesType), cel.Variable("msg_var", cel.ObjectType("test.Message")),
				fn("dummy_all_types", cel.Overload("dummy_all_types_overload",
					[]*cel.Type{cel.UintType, cel.DoubleType, cel.BoolType, cel.StringType, cel.BytesType, cel.ObjectType("test.Message")}, cel.BoolType)))
			r := must(t)(g.verifierFor(newEnv(t), verifier.FunctionAxioms(ax)).IsAlwaysTrue(compile(t, env,
				"dummy_all_types(uint_var, double_var, bool_var, string_var, bytes_var, msg_var) == true")))
			expectStatus(t, r, verifier.Verified)
		})
	})
	t.Run("translateFunctionCall_staticallyResolved_skipsDeadOverloads", func(t *testing.T) {
		requireZ3(t)
		var requested []string
		spy := func(id string) verifier.OverloadTranslator {
			return func(c *smt.Context, ts *verifier.TypeSystem, _ func(*smt.Term), _, _ []*smt.Term) (verifier.OverloadResult, bool) {
				requested = append(requested, id)
				return verifier.OverloadResult{Value: ts.WrapBool(c.MkTrue()), Approx: c.MkFalse()}, true
			}
		}
		ax := verifier.NewFunctionAxiom(decl("spy_func", ov("spy_func_int", types.BoolType, types.IntType), ov("spy_func_string", types.BoolType, types.StringType))).
			Overload("spy_func_int", spy("spy_func_int")).Overload("spy_func_string", spy("spy_func_string"))
		env := newEnv(t, fn("spy_func", cel.Overload("spy_func_int", []*cel.Type{cel.IntType}, cel.BoolType), cel.Overload("spy_func_string", []*cel.Type{cel.StringType}, cel.BoolType)))
		v, err := verifier.New(newEnv(t), verifier.FunctionAxioms(ax), verifier.Backend(testBackend()))
		if err != nil {
			t.Fatal(err)
		}
		if _, err := v.IsSatisfiable(compile(t, env, "spy_func(42) == true")); err != nil {
			t.Fatal(err)
		}
		if len(requested) != 1 || requested[0] != "spy_func_int" {
			t.Errorf("requested = %v", requested)
		}
	})
}

func TestLargeCounterexamplesTruncateOutput(t *testing.T) {
	ones := strings.TrimSuffix(strings.Repeat("1, ", 20), ", ")
	var entries []string
	for i := 0; i < 20; i++ {
		entries = append(entries, strconv.Itoa(i)+": 1")
	}
	for _, tc := range []struct {
		method, expr, want string
		v                  cel.EnvOption
	}{
		{"isAlwaysTrue_largeListCounterexample_truncatesOutput", "!(large_list == [" + ones + "])", "... (5 more elements)", cel.Variable("large_list", cel.ListType(cel.IntType))},
		{"isAlwaysTrue_largeMapCounterexample_truncatesOutput", "!(large_map == {" + strings.Join(entries, ", ") + "})", "... (5 more entries)", cel.Variable("large_map", cel.MapType(cel.IntType, cel.IntType))},
	} {
		tc := tc
		t.Run(tc.method, func(t *testing.T) {
			single(t, tc.method, func(t *testing.T, g *goldenRun) {
				env := newEnv(t, tc.v)
				r := must(t)(g.verifierFor(env, verifier.Timeout(10*time.Second)).IsAlwaysTrue(compile(t, env, tc.expr)))
				expectStatus(t, r, verifier.Violated)
				contains(t, r.Message(), tc.want)
			})
		})
	}
}

func TestCounterexampleMessageTwoFieldsFormatted(t *testing.T) {
	single(t, "counterexample_messageTwoFieldsFormatted", func(t *testing.T, g *goldenRun) {
		env := extendEnv(t, javaTestEnv(t), cel.Variable("msg", cel.ObjectType("cel.expr.conformance.proto3.TestAllTypes")))
		r := must(t)(g.verifier().IsAlwaysTrue(compile(t, env, "!(msg == TestAllTypes{single_int32: 1, single_int64: 2})")))
		expectStatus(t, r, verifier.Violated)
		contains(t, r.Message(), "single_int32: 1")
		contains(t, r.Message(), "single_int64: 2")
	})
}

// foldMacro builds a receiver macro expanding to a comprehension.
func foldMacro(name string, argc int, build func(eh parser.ExprHelper, target ast.Expr, args []ast.Expr) ast.Expr) cel.EnvOption {
	return cel.Macros(parser.NewReceiverMacro(name, argc, func(eh parser.ExprHelper, target ast.Expr, args []ast.Expr) (ast.Expr, *common.Error) {
		return build(eh, target, args), nil
	}))
}

func TestCustomComprehensions(t *testing.T) {
	t.Run("isAlwaysTrue_customComprehensionWithTrueAccuInit", func(t *testing.T) {
		single(t, "isAlwaysTrue_customComprehensionWithTrueAccuInit", func(t *testing.T, g *goldenRun) {
			env := newEnv(t, cel.Variable("dyn_list", cel.ListType(cel.DynType)),
				foldMacro("custom_fold", 1, func(eh parser.ExprHelper, target ast.Expr, _ []ast.Expr) ast.Expr {
					return eh.NewComprehension(target, "x", "accu", eh.NewLiteral(types.True), eh.NewLiteral(types.True),
						eh.NewCall(operators.LogicalNot, eh.NewIdent("accu")), eh.NewIdent("accu"))
				}))
			r := must(t)(g.verifierFor(env).IsAlwaysTrue(compile(t, env, "dyn_list == [1, 2] ? dyn_list.custom_fold(x) == true : true")))
			expectStatus(t, r, verifier.Verified)
		})
	})
	t.Run("isAlwaysTrue_customComprehensionWithLoopCondition_inconclusive", func(t *testing.T) {
		single(t, "isAlwaysTrue_customComprehensionWithLoopCondition_inconclusive", func(t *testing.T, g *goldenRun) {
			r := must(t)(g.verifier().IsAlwaysTrue(compile(t, javaTestEnv(t), "int_list == [1, 2] ? int_list.first_elem() == 2 : true")))
			if want := "Inconclusive: a counterexample may exist, but it depends on what the verifier doesn't model exactly: comprehensions with a loop condition."; r.Reason != want {
				t.Errorf("reason = %q", r.Reason)
			}
		})
	})
	t.Run("verifyEquivalence_comprehensionScopeShadowing_returnsInconclusive", func(t *testing.T) {
		single(t, "verifyEquivalence_comprehensionScopeShadowing_returnsInconclusive", func(t *testing.T, g *goldenRun) {
			mk := func(name, iterVar2 string) cel.EnvOption {
				return foldMacro(name, 1, func(eh parser.ExprHelper, target ast.Expr, args []ast.Expr) ast.Expr {
					return eh.NewComprehensionTwoVar(target, "unused", iterVar2, "x", args[0], eh.NewLiteral(types.True), eh.NewIdent(iterVar2), eh.NewIdent("x"))
				})
			}
			env := newEnv(t, cel.Variable("dyn_list", cel.ListType(cel.DynType)), mk("my_macro_1", "x"), mk("my_macro_2", "y"))
			v := g.verifierFor(env, verifier.ComprehensionUnrollLimit(0))
			r := must(t)(v.VerifyEquivalence(compile(t, env, "dyn_list.my_macro_1(true)"), compile(t, env, "dyn_list.my_macro_2(true)")))
			expectStatus(t, r, verifier.Inconclusive)
		})
	})
	t.Run("verifyEquivalence_comprehensionResultScopeIsolation_returnsInconclusive", func(t *testing.T) {
		single(t, "verifyEquivalence_comprehensionResultScopeIsolation_returnsInconclusive", func(t *testing.T, g *goldenRun) {
			env := newEnv(t, cel.Variable("dyn_list", cel.ListType(cel.DynType)), cel.Variable("x", cel.IntType), ext.Bindings(),
				foldMacro("my_macro", 1, func(eh parser.ExprHelper, target ast.Expr, args []ast.Expr) ast.Expr {
					return eh.NewComprehension(target, "x", "accu", args[0], eh.NewLiteral(types.True), eh.NewIdent("accu"),
						eh.NewCall(operators.Conditional,
							eh.NewCall(operators.Equals, eh.NewCall("size", eh.Copy(target)), eh.NewLiteral(types.Int(0))),
							eh.NewLiteral(types.Int(0)), eh.NewIdent("x")))
				}))
			v := g.verifierFor(env, verifier.ComprehensionUnrollLimit(0))
			r := must(t)(v.VerifyEquivalence(compile(t, env, "cel.bind(x, 10, dyn_list.my_macro(1))"), compile(t, env, "cel.bind(x, 20, dyn_list.my_macro(1))")))
			expectStatus(t, r, verifier.Inconclusive)
		})
	})
}

func TestVerifyImplicationSingles(t *testing.T) {
	const prefix = "Inconclusive: a counterexample may exist, but it depends on what the verifier doesn't model exactly: "
	impl := func(t *testing.T, v *verifier.Verifier, env *cel.Env, assume, assertion string) verifier.Result {
		return must(t)(v.VerifyImplication(compile(t, env, assume), compile(t, env, assertion), nil, "Implication"))
	}
	t.Run("verifyImplication_dynRangeComprehensionInAssumption_inconclusive", func(t *testing.T) {
		single(t, "verifyImplication_dynRangeComprehensionInAssumption_inconclusive", func(t *testing.T, g *goldenRun) {
			r := impl(t, g.verifier(), javaTestEnv(t), "dyn_var.exists(e, e == 1)", "x > 0")
			expectStatus(t, r, verifier.Inconclusive)
			if want := prefix + "comprehensions over `dyn` values."; r.Reason != want {
				t.Errorf("reason = %q", r.Reason)
			}
		})
	})
	t.Run("verifyImplication_approximateAssertionUnderDynRangeComprehension_inconclusive", func(t *testing.T) {
		single(t, "verifyImplication_approximateAssertionUnderDynRangeComprehension_inconclusive", func(t *testing.T, g *goldenRun) {
			env := extendEnv(t, javaTestEnv(t), fn("f", cel.Overload("f_int", []*cel.Type{cel.IntType}, cel.IntType)))
			r := impl(t, g.verifier(), env, "dyn_var.exists(e, e == 1)", "f(x) == f(x)")
			expectStatus(t, r, verifier.Inconclusive)
			if want := prefix + "comprehensions over `dyn` values, calls to `f`."; r.Reason != want {
				t.Errorf("reason = %q", r.Reason)
			}
		})
	})
	t.Run("verifyImplication_loopExceedsLimit_inconclusive", func(t *testing.T) {
		single(t, "verifyImplication_loopExceedsLimit_inconclusive", func(t *testing.T, g *goldenRun) {
			r := impl(t, g.verifier(verifier.ComprehensionUnrollLimit(2)), javaTestEnv(t), "int_list.all(x, x > 0)", "size(int_list) < 3 || int_list[2] > 0")
			expectStatus(t, r, verifier.Inconclusive)
			if want := prefix + "lists and maps longer than the unroll limit (2)."; r.Reason != want {
				t.Errorf("reason = %q", r.Reason)
			}
		})
	})
	t.Run("verifyImplication_exactUnknownAssumption_verified", func(t *testing.T) {
		single(t, "verifyImplication_exactUnknownAssumption_verified", func(t *testing.T, g *goldenRun) {
			r := impl(t, g.verifier(verifier.UnknownIdentifiers("b")), javaTestEnv(t), "b && !b", "dyn_var.exists(e, e == 1)")
			expectStatus(t, r, verifier.Verified)
		})
	})
}

func TestBmcMasking(t *testing.T) {
	t.Run("isSatisfiable_exactUnknownBesideUnmodeledComprehension_violated", func(t *testing.T) {
		single(t, "isSatisfiable_exactUnknownBesideUnmodeledComprehension_violated", func(t *testing.T, g *goldenRun) {
			r := must(t)(g.verifier(verifier.UnknownIdentifiers("b")).IsSatisfiable(compile(t, javaTestEnv(t), "(false && int_list.first_elem() == 1) || (b && !b)")))
			expectStatus(t, r, verifier.Violated)
		})
	})
	t.Run("isSatisfiable_maskedByBmcButAlwaysFalse_returnsFailed", func(t *testing.T) {
		single(t, "isSatisfiable_maskedByBmcButAlwaysFalse_returnsFailed", func(t *testing.T, g *goldenRun) {
			r := must(t)(g.verifier(verifier.ComprehensionUnrollLimit(3)).IsSatisfiable(compile(t, javaTestEnv(t), "int_list == [1, 2, 3, 4] ? int_list.exists(x, x == 42) && false : false")))
			expectStatus(t, r, verifier.Violated)
		})
	})
	t.Run("verifyEquivalence_maskedByBmcButAlwaysEqual_returnsVerified", func(t *testing.T) {
		single(t, "verifyEquivalence_maskedByBmcButAlwaysEqual_returnsVerified", func(t *testing.T, g *goldenRun) {
			env := javaTestEnv(t)
			r := must(t)(g.verifier(verifier.ComprehensionUnrollLimit(3)).VerifyEquivalence(
				compile(t, env, "int_list == [1, 2, 3, 4] ? int_list.all(x, x > 0) && false : false"),
				compile(t, env, "int_list == [1, 2, 3, 4] ? int_list.all(x, x > 1) && false : false")))
			expectStatus(t, r, verifier.Verified)
		})
	})
	runTable(t, "EquivalenceZeroUnrollLimitTestCase", "verifyEquivalence_zeroUnrollLimit_returnsInconclusive", func(t *testing.T, g *goldenRun, c map[string]any) {
		env := javaTestEnv(t)
		r := must(t)(g.verifier(verifier.ComprehensionUnrollLimit(0)).VerifyEquivalence(compile(t, env, str(c, "exprA")), compile(t, env, str(c, "exprB"))))
		expectStatus(t, r, verifier.Inconclusive)
	})
	runTable(t, "EquivalenceZeroUnrollLimitVerifiedTestCase", "verifyEquivalence_zeroUnrollLimit_twoVarComprehensions_returnsVerified", func(t *testing.T, g *goldenRun, c map[string]any) {
		env := javaTestEnv(t)
		r := must(t)(g.verifier(verifier.ComprehensionUnrollLimit(0)).VerifyEquivalence(compile(t, env, str(c, "exprA")), compile(t, env, str(c, "exprB"))))
		expectStatus(t, r, verifier.Verified)
	})
}

func TestIsAlwaysTrueConstantVarDeclVerified(t *testing.T) {
	single(t, "isAlwaysTrue_constantVarDecl_verified", func(t *testing.T, g *goldenRun) {
		env := newEnv(t, cel.Constant("CONST_INT", cel.IntType, types.Int(42)))
		r := must(t)(g.verifierFor(env).IsAlwaysTrue(compile(t, env, "CONST_INT == 42 && [1, 2].all(x, .CONST_INT == 42 && x > 0)")))
		expectStatus(t, r, verifier.Verified)
	})
}
