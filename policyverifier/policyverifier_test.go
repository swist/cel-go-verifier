package policyverifier_test

import (
	"encoding/json"
	"os"
	"regexp"
	"strings"
	"testing"

	"cel.dev/cel-go/cel"
	"cel.dev/cel-go/common/types"
	"cel.dev/cel-go/ext"
	"cel.dev/cel-go/policy"
	proto3pb "cel.dev/expr/conformance/proto3"

	"github.com/swist/cel-go-verifier/internal/goldentest"
	"github.com/swist/cel-go-verifier/internal/smtdiff"
	"github.com/swist/cel-go-verifier/policyverifier"
	"github.com/swist/cel-go-verifier/smt/z3proc"
	"github.com/swist/cel-go-verifier/verifier"
)

// Ports of cel-java's CelPolicyVerifierImplTest.

const goldenDir = "../testdata/golden/java"

// cel-go's policy compiler composes rules differently from cel-java's, so the
// composed expressions (and transcripts) of policies with several matches
// differ; the outcomes don't.
var strictGolden = os.Getenv("STRICT_POLICY_GOLDEN") != ""

func baseEnv(t testing.TB, opts ...cel.EnvOption) *cel.Env {
	t.Helper()
	env, err := cel.NewEnv(append([]cel.EnvOption{
		cel.CrossTypeNumericComparisons(true),
		ext.Bindings(),
		cel.Types(&proto3pb.TestAllTypes{}),
		cel.Variable("x", cel.IntType),
		cel.Variable("y", cel.IntType),
		cel.Variable("a", cel.BoolType),
		cel.Variable("b", cel.BoolType),
		cel.Variable("role", cel.StringType),
		cel.Variable("country", cel.StringType),
		cel.Variable("port", cel.IntType),
		cel.Variable("request", cel.DynType),
		cel.Variable("test_all_types", cel.ObjectType("cel.expr.conformance.proto3.TestAllTypes")),
	}, opts...)...)
	if err != nil {
		t.Fatal(err)
	}
	return env
}

var javaTypes []string

func typeProvider(t testing.TB, env *cel.Env) verifier.TypeProvider {
	if javaTypes == nil {
		b, err := os.ReadFile("../testdata/golden/testcases.json")
		if err != nil {
			t.Fatal(err)
		}
		var raw map[string]json.RawMessage
		if err := json.Unmarshal(b, &raw); err != nil {
			t.Fatal(err)
		}
		_ = json.Unmarshal(raw["types:CelPolicyVerifierImplTest.CEL"], &javaTypes)
	}
	var names []string
	for _, n := range javaTypes {
		if tp, ok := env.CELTypeProvider().FindStructType(n); ok && tp.Parameters()[0].Kind() == types.StructKind {
			names = append(names, n)
		}
	}
	return verifier.NewProtoTypeProvider(env.CELTypeProvider(), proto3pb.File_cel_expr_conformance_proto3_test_all_types_proto).WithOrder(names)
}

type run struct {
	t   *testing.T
	rec *smtdiff.Recorder
}

func newRun(t *testing.T) *run {
	if !z3proc.New().Available() {
		t.Skip("z3 not found; set Z3_PATH")
	}
	return &run{t, &smtdiff.Recorder{}}
}

// verifier mirrors CelPolicyVerifierFactory.newVerifier(compiler(env), CelVerifierFactory.newVerifier(CEL)).
func (r *run) verifier(env *cel.Env, opts ...verifier.Option) *policyverifier.Verifier {
	base := baseEnv(r.t)
	v, err := verifier.New(base, append([]verifier.Option{verifier.Types(typeProvider(r.t, base)), verifier.Recorder(r.rec.Factory())}, opts...)...)
	if err != nil {
		r.t.Fatal(err)
	}
	return policyverifier.New(env, v)
}

func (r *run) check(name string) {
	t := r.t
	t.Helper()
	diff, found, err := goldentest.Compare(goldenDir, "CelPolicyVerifierImplTest."+name, r.rec.String())
	switch {
	case err != nil:
		t.Fatal(err)
	case !found:
		t.Logf("no golden for %s", name)
	case diff != "" && strictGolden:
		t.Errorf("transcript differs from cel-java: %s", diff)
	case diff != "":
		t.Logf("transcript differs from cel-java (policy composition): %s", truncate(diff, 300))
	}
}

func truncate(s string, n int) string {
	if len(s) > n {
		return s[:n] + "…"
	}
	return s
}

func parse(t *testing.T, src string) *policy.Policy {
	t.Helper()
	p, err := policyverifier.Parse(src, "<policy>")
	if err != nil {
		t.Fatal(err)
	}
	return p
}

func load(t *testing.T, name string) *policy.Policy {
	t.Helper()
	b, err := os.ReadFile("testdata/" + name)
	if err != nil {
		t.Fatal(err)
	}
	return parse(t, string(b))
}

func invariants(t *testing.T, pv *policyverifier.Verifier, p *policy.Policy) map[string]verifier.Result {
	t.Helper()
	rs, err := pv.VerifyInvariants(p)
	if err != nil {
		t.Fatal(err)
	}
	out := map[string]verifier.Result{}
	for _, r := range rs {
		out[r.ID] = r.Result
	}
	return out
}

func expectStatus(t *testing.T, r verifier.Result, want verifier.Status) {
	t.Helper()
	if r.Status != want {
		t.Errorf("status = %v, want %v: %s", r.Status, want, r.Message())
	}
}

func TestVerifyEquivalenceSuccess(t *testing.T) {
	b, err := os.ReadFile("../testdata/golden/testcases.json")
	if err != nil {
		t.Fatal(err)
	}
	var all map[string]json.RawMessage
	if err := json.Unmarshal(b, &all); err != nil {
		t.Fatal(err)
	}
	var cases []map[string]string
	if err := json.Unmarshal(all["CelPolicyVerifierImplTest.EquivalenceTestCase"], &cases); err != nil {
		t.Fatal(err)
	}
	for _, c := range cases {
		c := c
		t.Run(c["name"], func(t *testing.T) {
			r := newRun(t)
			res, err := r.verifier(baseEnv(t)).VerifyEquivalence(parse(t, c["policySourceA"]), parse(t, c["policySourceB"]))
			if err != nil {
				t.Fatal(err)
			}
			expectStatus(t, res, verifier.Verified)
			r.check("verifyEquivalence_success[" + c["name"] + "]")
		})
	}
}

func TestVerifyEquivalenceViolation(t *testing.T) {
	r := newRun(t)
	res, err := r.verifier(baseEnv(t)).VerifyEquivalence(
		parse(t, "name: pA\nrule:\n  match:\n    - output: 'x > 10'"),
		parse(t, "name: pB\nrule:\n  match:\n    - output: 'x > 5'"))
	if err != nil {
		t.Fatal(err)
	}
	expectStatus(t, res, verifier.Violated)
	if !regexp.MustCompile(`Equivalence violation detected\. Counterexample input:\n {2}x = (6|7|8|9|10)`).MatchString(res.Message()) {
		t.Errorf("message = %q", res.Message())
	}
	r.check("verifyEquivalence_violation_throws")
}

func TestVerifyInvariants(t *testing.T) {
	boolVars := []cel.EnvOption{
		cel.Variable("is_admin", cel.BoolType), cel.Variable("is_owner", cel.BoolType),
		cel.Variable("is_privileged", cel.BoolType), cel.Variable("is_prod", cel.BoolType),
		cel.Variable("has_approval", cel.BoolType), cel.Variable("spec", cel.DynType),
	}
	t.Run("emptyInvariants_returnsEmptyMap", func(t *testing.T) {
		r := newRun(t)
		if got := invariants(t, r.verifier(baseEnv(t)), parse(t, "name: empty_policy\nrule:\n  match:\n    - output: 'true'")); len(got) != 0 {
			t.Errorf("results = %v", got)
		}
	})
	t.Run("flawedPolicy_violationDetected", func(t *testing.T) {
		r := newRun(t)
		res := invariants(t, r.verifier(baseEnv(t)), load(t, "flawed_policy.yaml"))["always_secure"]
		expectStatus(t, res, verifier.Violated)
		if !strings.Contains(res.Message(), "port = 80") {
			t.Errorf("message = %q", res.Message())
		}
		r.check("verifyInvariants_flawedPolicy_violationDetected")
	})
	t.Run("secureResourceAccess_verified", func(t *testing.T) {
		r := newRun(t)
		res := invariants(t, r.verifier(baseEnv(t, cel.Variable("resource", cel.DynType))), load(t, "secure_resource_access.yaml"))
		expectStatus(t, res["no_unprivileged_break_glass"], verifier.Verified)
		r.check("verifyInvariants_secureResourceAccess_verified")
	})
	t.Run("multipleInvariants_mixedResults", func(t *testing.T) {
		r := newRun(t)
		res := invariants(t, r.verifier(baseEnv(t)), load(t, "multi_invariant_policy.yaml"))
		if len(res) != 2 {
			t.Fatalf("results = %v", res)
		}
		expectStatus(t, res["admin_granted"], verifier.Verified)
		expectStatus(t, res["viewer_granted"], verifier.Violated)
		if !strings.Contains(res["viewer_granted"].Message(), `role = "viewer"`) {
			t.Errorf("message = %q", res["viewer_granted"].Message())
		}
		r.check("verifyInvariants_multipleInvariants_mixedResults")
	})
	for name, src := range map[string]string{
		"invalidAssumeClause": "name: invalid_assume\nrule:\n  match:\n    - output: 'true'\nverification:\n  invariants:\n    - id: bad_assume\n      assume: non_existent_var == 123\n      assert: rule.result == true",
		"invalidAssertClause": "name: invalid_assert\nrule:\n  match:\n    - output: 'true'\nverification:\n  invariants:\n    - id: bad_assert\n      assert: rule.result + non_existent_var == true",
	} {
		src := src
		t.Run(name+"_throwsValidationException", func(t *testing.T) {
			r := newRun(t)
			if _, err := r.verifier(baseEnv(t)).VerifyInvariants(parse(t, src)); err == nil {
				t.Error("no error")
			} else if _, ok := err.(*policyverifier.ValidationError); !ok {
				t.Errorf("err = %T %v", err, err)
			}
		})
	}
	t.Run("restrictedDestinationsPolicy_verified", func(t *testing.T) {
		r := newRun(t)
		env := baseEnv(t, cel.Variable("origin", cel.DynType), cel.Variable("destination", cel.DynType),
			cel.Variable("spec", cel.DynType), cel.Variable("resource", cel.DynType),
			cel.Function("locationCode", cel.Overload("locationCode_string", []*cel.Type{cel.StringType}, cel.StringType)))
		res := invariants(t, r.verifier(env), load(t, "restricted_destinations_policy.yaml"))
		for _, id := range []string{"restricted_by_nationality_prohibited", "restricted_by_origin_ip_prohibited", "unrestricted_destination_allowed"} {
			expectStatus(t, res[id], verifier.Verified)
		}
		r.check("verifyInvariants_restrictedDestinationsPolicy_verified")
	})
	for _, tc := range []struct {
		name, src string
		results   map[string]verifier.Status
		opts      []verifier.Option
	}{
		{"invariantReferencesPolicyVariable_verified", "name: variable_reference_policy\nrule:\n  variables:\n    - is_admin: role == 'admin'\n  match:\n    - condition: variables.is_admin\n      output: 'true'\n    - output: 'false'\nverification:\n  invariants:\n    - id: admin_always_true\n      assume: variables.is_admin\n      assert: rule.result == true",
			map[string]verifier.Status{"admin_always_true": verifier.Verified}, nil},
		{"verificationVariablesAndMultiClauseLists_verified", "name: verification_ergonomics_policy\nrule:\n  variables:\n    - rule_admin: role == 'admin'\n  match:\n    - condition: variables.rule_admin\n      output: 'true'\n    - output: 'false'\nverification:\n  variables:\n    - ver_admin: variables.rule_admin && true\n  invariants:\n    - id: ergonomic_inv\n      assume:\n        - variables.ver_admin\n        - role != 'editor'\n      assert:\n        - rule.result == true\n        - role == 'admin'",
			map[string]verifier.Status{"ergonomic_inv": verifier.Verified}, nil},
		{"literalListVariableBeyondUnrollLimit_verified", "name: literal_list_policy\nrule:\n  variables:\n    - xs: '[1, 2, 3, 4, 5, 6]'\n  match:\n    - output: 'true'\nverification:\n  invariants:\n    - id: all_positive\n      assert: variables.xs.all(x, x > 0)",
			map[string]verifier.Status{"all_positive": verifier.Verified}, []verifier.Option{verifier.ComprehensionUnrollLimit(5)}},
		{"unrelatedBoundedSymbolApproximate_doesNotForceInconclusive", "name: unrelated_approx_policy\nrule:\n  variables:\n    - unrelated_approx: 'request.matches(\"a\") == true'\n  match:\n    - condition: 'port == 80'\n      output: 'true'\n    - output: 'false'\nverification:\n  invariants:\n    - id: port_check\n      assume:\n        - 'port == 80'\n      assert:\n        - 'rule.result == true'\n",
			map[string]verifier.Status{"port_check": verifier.Verified}, nil},
		{"verificationVariablesCanReferenceRuleResult", "name: rule_result_in_ver_var_policy\nrule:\n  match:\n    - condition: 'port == 80'\n      output: 'true'\n    - output: 'false'\nverification:\n  variables:\n    - is_denied: 'rule.result == false'\n  invariants:\n    - id: port_check\n      assume:\n        - 'port == 80'\n      assert:\n        - 'variables.is_denied == false'\n",
			map[string]verifier.Status{"port_check": verifier.Verified}, nil},
		{"boundedSymbolWithApproximation_returnsInconclusive", "name: approx_symbol_policy\nrule:\n  variables:\n    - approx_var: 'request.matches(\"^[a-z]+$\") == true'\n  match:\n    - condition: 'variables.approx_var'\n      output: 'true'\n    - output: 'false'\nverification:\n  invariants:\n    - id: check_approx\n      assert:\n        - 'variables.approx_var == true'\n",
			map[string]verifier.Status{"check_approx": verifier.Inconclusive}, nil},
	} {
		tc := tc
		t.Run(tc.name, func(t *testing.T) {
			r := newRun(t)
			res := invariants(t, r.verifier(baseEnv(t), tc.opts...), parse(t, tc.src))
			for id, want := range tc.results {
				expectStatus(t, res[id], want)
			}
			r.check("verifyInvariants_" + tc.name)
		})
	}
	t.Run("workloadAdmissionFlawed_violationsDetected", func(t *testing.T) {
		r := newRun(t)
		res := invariants(t, r.verifier(baseEnv(t, boolVars...)), load(t, "workload_admission_flawed.yaml"))["universal_no_unapproved_privileged_prod"]
		expectStatus(t, res, verifier.Violated)
		// cel-java finds is_admin = true; cel-go's composition leads Z3 to the other bypass,
		// is_owner = true. Both violate the invariant.
		re := regexp.MustCompile(`^Invariant 'universal_no_unapproved_privileged_prod' violation detected\. Counterexample input:\n` +
			`  is_admin = (true|false)\n  is_owner = (true|false)\n  is_privileged = true\n  is_prod = true\n  has_approval = false$`)
		if m := re.FindStringSubmatch(res.Message()); m == nil || (m[1] != "true" && m[2] != "true") {
			t.Errorf("message = %q", res.Message())
		}
		r.check("verifyInvariants_workloadAdmissionFlawed_violationsDetected")
	})
	t.Run("workloadAdmissionFixed_verified", func(t *testing.T) {
		r := newRun(t)
		res := invariants(t, r.verifier(baseEnv(t, boolVars...)), load(t, "workload_admission_fixed.yaml"))["universal_no_unapproved_privileged_prod"]
		expectStatus(t, res, verifier.Verified)
		r.check("verifyInvariants_workloadAdmissionFixed_verified")
	})
	for name, tc := range map[string]struct{ src, desc string }{
		"invariantSyntaxError":            {"name: syntax_error_policy\nrule:\n  match:\n    - output: 'true'\nverification:\n  invariants:\n    - id: bad_invariant\n      assume:\n        - 'port == 80 &&+ port == 90'\n      assert:\n        - 'rule.result == false'\n", "invariant.bad_invariant.assume:1:14"},
		"verificationVariableSyntaxError": {"name: syntax_error_policy\nrule:\n  match:\n    - output: 'true'\nverification:\n  variables:\n    - bad_var: 'port == 80 &&+ port == 90'\n  invariants:\n    - id: always_secure\n      assert:\n        - 'rule.result == false'\n", "verification.variables.bad_var:1:14"},
	} {
		tc := tc
		t.Run(name+"_formatsSnippetAndDescription", func(t *testing.T) {
			r := newRun(t)
			_, err := r.verifier(baseEnv(t)).VerifyInvariants(parse(t, tc.src))
			// cel-go's parser words syntax errors differently from cel-java's.
			if err == nil || !strings.Contains(err.Error(), "ERROR: "+tc.desc) || !strings.Contains(err.Error(), "| port == 80 &&+ port == 90\n | .............^") {
				t.Errorf("err = %v", err)
			}
		})
	}
}
