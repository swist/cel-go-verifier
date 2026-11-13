package verifier_test

import (
	"strings"
	"testing"

	"cel.dev/cel-go/cel"
	"cel.dev/cel-go/common/types"

	"github.com/swist/cel-go-verifier/verifier"
)

// Ports of the individual (non-table) tests of CelVerifierZ3ImplTest.

// single runs a test with a golden transcript named after the Java test method.
func single(t *testing.T, method string, fn func(t *testing.T, g *goldenRun)) {
	t.Helper()
	g := newGoldenRun(t, z3+method)
	fn(t, g)
	g.check()
}

func must(t *testing.T) func(verifier.Result, error) verifier.Result {
	return func(r verifier.Result, err error) verifier.Result {
		t.Helper()
		if err != nil {
			t.Fatal(err)
		}
		return r
	}
}

func contains(t *testing.T, s, sub string) {
	t.Helper()
	if !strings.Contains(s, sub) {
		t.Errorf("%q doesn't contain %q", s, sub)
	}
}

func notContains(t *testing.T, s, sub string) {
	t.Helper()
	if strings.Contains(s, sub) {
		t.Errorf("%q contains %q", s, sub)
	}
}

func matches(t *testing.T, s, re string) {
	t.Helper()
	if !javaContainsMatch(re, s) {
		t.Errorf("%q doesn't match %q", s, re)
	}
}

func eval(t *testing.T, env *cel.Env, a *cel.Ast, vars map[string]any) any {
	t.Helper()
	p, err := env.Program(a)
	if err != nil {
		t.Fatal(err)
	}
	out, _, err := p.Eval(vars)
	if err != nil {
		t.Fatalf("eval: %v", err)
	}
	return out.Value()
}

func TestIsSatisfiableWithVariableReturnsSatisfyingModel(t *testing.T) {
	single(t, "isSatisfiable_withVariable_returnsSatisfyingModel", func(t *testing.T, g *goldenRun) {
		r := must(t)(g.verifier().IsSatisfiable(compile(t, javaTestEnv(t), "x > 5")))
		expectStatus(t, r, verifier.Verified)
		contains(t, r.Message(), "Condition is satisfiable.")
		contains(t, r.Message(), "Satisfying input:")
		matches(t, r.Message(), `x = (?:[6-9]|[1-9]\d+)`)
	})
}

func TestIsSatisfiableWitnessValueSatisfiesExpressionAndDisplayRoundTrips(t *testing.T) {
	runTable(t, "WitnessTestCase", "isSatisfiable_witnessValueSatisfiesExpressionAndDisplayRoundTrips", func(t *testing.T, g *goldenRun, c map[string]any) {
		env := javaTestEnv(t)
		a := compile(t, env, str(c, "expr"))
		r := must(t)(g.verifier().IsSatisfiable(a))
		name := str(c, "variableName")
		if r.Witness == nil {
			t.Fatalf("no witness: %s", r.Message())
		}
		v := r.Witness.Variables[name]
		if v.Display != str(c, "expectedDisplayValue") {
			t.Errorf("display = %q, want %q", v.Display, str(c, "expectedDisplayValue"))
		}
		if v.Value == nil {
			if celGoDurationLimit[str(c, "name")] {
				t.Skipf("cel-go can't represent %s: its durations are time.Durations", v.Display)
			}
			t.Fatalf("no exact value for %s", name)
		}
		vars := map[string]any{name: v.Value}
		if out := eval(t, env, a, vars); out != true {
			t.Errorf("witness doesn't satisfy the expression: %v", out)
		}
		rt := compile(t, env, name+" == "+v.Display)
		if out := eval(t, env, rt, vars); out != true {
			t.Errorf("display doesn't round trip: %v", out)
		}
	})
}

// celGoDurationLimit lists witnesses beyond the range of cel-go durations (about ±292 years).
var celGoDurationLimit = map[string]bool{"MIN_DURATION": true, "MAX_DURATION": true}

func TestIsSatisfiableNoExactRuntimeValueWitnessValueEmpty(t *testing.T) {
	runTable(t, "InexactWitnessTestCase", "isSatisfiable_noExactRuntimeValue_witnessValueEmpty", func(t *testing.T, g *goldenRun, c map[string]any) {
		r := must(t)(g.verifier().IsSatisfiable(compile(t, javaTestEnv(t), str(c, "expr"))))
		if r.Witness == nil {
			t.Fatalf("no witness: %s", r.Message())
		}
		if v := r.Witness.Variables[str(c, "variableName")]; v.Value != nil {
			t.Errorf("value = %v, want none (display %s)", v.Value, v.Display)
		}
	})
}

func TestIsSatisfiableListAtDisplayLimitDisplaysAllElements(t *testing.T) {
	single(t, "isSatisfiable_listAtDisplayLimit_displaysAllElements", func(t *testing.T, g *goldenRun) {
		r := must(t)(g.verifier().IsSatisfiable(compile(t, javaTestEnv(t), "int_list == [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]")))
		if !strings.HasSuffix(r.Message(), "int_list = [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]") {
			t.Errorf("message = %q", r.Message())
		}
	})
}

func TestIsSatisfiableListPastDisplayLimitElidesRemainingElements(t *testing.T) {
	single(t, "isSatisfiable_listPastDisplayLimit_elidesRemainingElements", func(t *testing.T, g *goldenRun) {
		v := g.verifier(verifier.ComprehensionUnrollLimit(16))
		r := must(t)(v.IsSatisfiable(compile(t, javaTestEnv(t), "int_list == [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]")))
		if !strings.HasSuffix(r.Message(), "int_list = [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, ... (1 more elements)]") {
			t.Errorf("message = %q", r.Message())
		}
	})
}

func TestIsSatisfiableNoContainerError(t *testing.T) {
	for _, tc := range []struct{ method, expr, want string }{
		{"isSatisfiable_mapNoContainerError_returnsSatisfyingModel", "string_int_map.size() == 1", "string_int_map = {"},
		{"isSatisfiable_listNoContainerError_returnsSatisfyingModel", "dyn_list.size() == 1", "dyn_list = ["},
		{"isSatisfiable_dynMapNoContainerError_returnsSatisfyingModel", "dyn_map.size() == 1", "dyn_map = {"},
	} {
		tc := tc
		t.Run(tc.method, func(t *testing.T) {
			single(t, tc.method, func(t *testing.T, g *goldenRun) {
				r := must(t)(g.verifier().IsSatisfiable(compile(t, javaTestEnv(t), tc.expr)))
				expectStatus(t, r, verifier.Verified)
				contains(t, r.Message(), "Condition is satisfiable.")
				contains(t, r.Message(), "Satisfying input:")
				contains(t, r.Message(), tc.want)
				notContains(t, r.Message(), "Error")
			})
		})
	}
}

func TestCounterexampleNullValueFormattedAsNull(t *testing.T) {
	single(t, "counterexample_nullValueFormattedAsNull", func(t *testing.T, g *goldenRun) {
		r := must(t)(g.verifier().IsSatisfiable(compile(t, javaTestEnv(t), "unknown_var == 3u && request == null")))
		expectStatus(t, r, verifier.Verified)
		contains(t, r.Message(), "request = null")
	})
}

func TestCounterexampleMapFormattedCorrectly(t *testing.T) {
	single(t, "counterexample_mapFormattedCorrectly", func(t *testing.T, g *goldenRun) {
		r := must(t)(g.verifier().IsSatisfiable(compile(t, javaTestEnv(t), "string_int_map.size() == 2 && string_int_map['a'] == 1")))
		expectStatus(t, r, verifier.Verified)
		matches(t, r.Message(), `string_int_map = \{[^}]*,[^}]*\}`)
		contains(t, r.Message(), `"a": 1`)
	})
}

func TestIsAlwaysTrueCounterexampleNeverContainsError(t *testing.T) {
	runTable(t, "CounterexampleNeverErrorTestCase", "isAlwaysTrue_counterexampleNeverContainsError", func(t *testing.T, g *goldenRun, c map[string]any) {
		r := must(t)(g.verifier().IsAlwaysTrue(compile(t, javaTestEnv(t), str(c, "expr"))))
		expectStatus(t, r, verifier.Violated)
		notContains(t, r.Message(), "Error")
	})
}

func TestIsSatisfiableUnconditionalReturnsUnconditionalMessage(t *testing.T) {
	single(t, "isSatisfiable_unconditional_returnsUnconditionalMessage", func(t *testing.T, g *goldenRun) {
		r := must(t)(g.verifier().IsSatisfiable(compile(t, javaTestEnv(t), "1 + 1 == 2")))
		expectStatus(t, r, verifier.Verified)
		if want := "Condition is satisfiable. (The expression is satisfiable unconditionally, regardless of input state)"; r.Message() != want {
			t.Errorf("message = %q, want %q", r.Message(), want)
		}
	})
}

const inconclusiveSatPrefix = "Inconclusive: a satisfying input may exist, but it depends on what the verifier doesn't model exactly: "

func TestIsSatisfiableApproximateListsApproximationSources(t *testing.T) {
	runTable(t, "ApproximationSourceTestCase", "isSatisfiable_approximate_listsApproximationSources", func(t *testing.T, g *goldenRun, c map[string]any) {
		r := must(t)(g.verifier().IsSatisfiable(compile(t, javaTestEnv(t), str(c, "expr"))))
		expectStatus(t, r, verifier.Inconclusive)
		if want := inconclusiveSatPrefix + str(c, "expectedSources") + "."; r.Reason != want {
			t.Errorf("reason = %q, want %q", r.Reason, want)
		}
	})
}

// fgEnv extends the test environment with the uninterpreted functions f and g.
func fgEnv(t testing.TB) *cel.Env {
	env, err := javaTestEnv(t).Extend(
		cel.Function("f", cel.Overload("f_int", []*cel.Type{cel.IntType}, cel.IntType)),
		cel.Function("g", cel.Overload("g_int", []*cel.Type{cel.IntType}, cel.IntType)))
	if err != nil {
		t.Fatal(err)
	}
	return env
}

func TestIsSatisfiableUninterpretedFunctionsListsApproximationSources(t *testing.T) {
	runTable(t, "UninterpretedFunctionSourceTestCase", "isSatisfiable_uninterpretedFunctions_listsApproximationSources", func(t *testing.T, g *goldenRun, c map[string]any) {
		r := must(t)(g.verifier().IsSatisfiable(compile(t, fgEnv(t), str(c, "expr"))))
		expectStatus(t, r, verifier.Inconclusive)
		if want := inconclusiveSatPrefix + str(c, "expectedSources") + "."; r.Reason != want {
			t.Errorf("reason = %q, want %q", r.Reason, want)
		}
	})
}

func TestIsSatisfiableApproximateReturnsPotentialSatisfyingInput(t *testing.T) {
	single(t, "isSatisfiable_approximate_returnsPotentialSatisfyingInput", func(t *testing.T, g *goldenRun) {
		r := must(t)(g.verifier().IsSatisfiable(compile(t, javaTestEnv(t), "int('123') == 123 ? x > 5 : false")))
		expectStatus(t, r, verifier.Inconclusive)
		contains(t, r.Message(), "Inconclusive: a satisfying input may exist")
		contains(t, r.Message(), "Potential satisfying input:")
		matches(t, r.Message(), `x = (?:[6-9]|[1-9]\d+)`)
	})
}

var _ = types.IntType
