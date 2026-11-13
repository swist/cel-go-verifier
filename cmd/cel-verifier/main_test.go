package main

// Ports of cel-java's CelVerifierToolTest, FormatUtilsTest and
// VerificationOptionsTest. Tests that reach the solver compare their
// transcripts with the cel-java goldens.

import (
	"bytes"
	"os"
	"path/filepath"
	"strings"
	"testing"
	"time"

	"cel.dev/cel-go/cel"

	"github.com/swist/cel-go-verifier/internal/goldentest"
	"github.com/swist/cel-go-verifier/internal/smtdiff"
	"github.com/swist/cel-go-verifier/smt/z3proc"
	"github.com/swist/cel-go-verifier/verifier"
)

const goldenDir = "../../testdata/golden/java"

func requireZ3(t *testing.T) {
	t.Helper()
	if !z3proc.New().Available() {
		t.Skip("z3 not found; set Z3_PATH")
	}
}

// golden records the solver interactions of the test and compares them with
// the cel-java golden of the same name when the test ends. Policy transcripts
// differ because cel-go composes policies differently (cel.@block), so they
// are compared only with STRICT_POLICY_GOLDEN set.
func golden(t *testing.T, policy bool) {
	t.Helper()
	requireZ3(t)
	rec := &smtdiff.Recorder{}
	recorderHook = rec.Factory()
	t.Cleanup(func() {
		recorderHook = nil
		name := "CelVerifierToolTest." + t.Name()[strings.Index(t.Name(), "/")+1:]
		diff, found, err := goldentest.Compare(goldenDir, name, rec.String())
		switch {
		case err != nil:
			t.Fatal(err)
		case !found:
			t.Logf("no golden %s", name)
		case diff != "" && policy && os.Getenv("STRICT_POLICY_GOLDEN") == "":
			t.Logf("policy transcript differs from cel-java's (expected: cel-go composes policies differently)")
		case diff != "":
			t.Errorf("transcript differs from cel-java's:\n%s", diff)
		}
	})
}

func tool(args ...string) (int, string) {
	var out bytes.Buffer
	code := run(args, &out, &out)
	return code, out.String()
}

func opts5s() options { o := defaultOptions(); o.timeout = 5 * time.Second; return o }

func mustVars(t *testing.T, specs ...string) []variable {
	t.Helper()
	v, err := parseVariables(specs)
	if err != nil {
		t.Fatal(err)
	}
	return v
}

func writePolicy(t *testing.T, name, content string) string {
	t.Helper()
	path := filepath.Join(t.TempDir(), name)
	if err := os.WriteFile(path, []byte(content), 0o644); err != nil {
		t.Fatal(err)
	}
	return path
}

func mustContain(t *testing.T, got string, wants ...string) {
	t.Helper()
	for _, w := range wants {
		if !strings.Contains(got, w) {
			t.Errorf("output %q doesn't contain %q", got, w)
		}
	}
}

func wantCode(t *testing.T, got, want int, out string) {
	t.Helper()
	if got != want {
		t.Errorf("exit code = %d, want %d; output:\n%s", got, want, out)
	}
}

const portPolicyHead = "rule:\n" +
	"  match:\n" +
	"    - condition: port == 80\n" +
	"      output: 'true'\n" +
	"    - output: 'false'\n" +
	"verification:\n" +
	"  invariants:\n"

func TestTool(t *testing.T) {
	t.Run("celVerifierTool_checkSat_jsonOutputFormat", func(t *testing.T) {
		golden(t, false)
		_, out := tool("check-sat", "--expr", "x > 0", "--var", "x:int", "--output_format", "json")
		if !strings.HasPrefix(out, "{\n") || !strings.HasSuffix(strings.TrimSpace(out), "}") {
			t.Errorf("not a JSON object: %q", out)
		}
		mustContain(t, out, `"status": "VERIFIED"`, "satisfiable")
	})
	t.Run("celVerifierTool_checkSat_textOutputFormat", func(t *testing.T) {
		golden(t, false)
		_, out := tool("check-sat", "--expr", "x > 0", "--var", "x:int", "-fmt", "text")
		mustContain(t, out, "[VERIFIED]", "satisfiable")
	})
	t.Run("celVerifierTool_checkSat_withDynVariable", func(t *testing.T) {
		golden(t, false)
		_, out := tool("check-sat", "--expr", "x == 'hello'", "--var", "x:dyn", "-fmt", "json")
		mustContain(t, out, `"status": "VERIFIED"`)
	})
	t.Run("celVerifierTool_checkSat_withUnknownOption", func(t *testing.T) {
		golden(t, false)
		_, out := tool("check-sat", "--expr", "request.headers != null", "--var", "request:map<string, dyn>",
			"-u", "request.headers", "-fmt", "json")
		mustContain(t, out, `"status": "VERIFIED"`)
	})
	t.Run("celVerifierTool_checkSat_withTimeoutAndUnrollLimit", func(t *testing.T) {
		golden(t, false)
		_, out := tool("check-sat", "--expr", "[1, 2, 3].all(x, x > 0)", "--timeout", "5", "--unroll-limit", "5", "-fmt", "json")
		mustContain(t, out, `"status": "VERIFIED"`)
	})
	t.Run("celVerifierTool_checkSat_withTimestampDurationAndOptional", func(t *testing.T) {
		golden(t, false)
		_, out := tool("check-sat", "--expr", "t + d > timestamp(1000) && opt.hasValue()",
			"--var", "t:timestamp", "--var", "d:duration", "--var", "opt:optional<int>", "-fmt", "json")
		mustContain(t, out, `"status": "VERIFIED"`)
	})
	t.Run("celVerifierTool_verifyPolicy_fileNotFound", func(t *testing.T) {
		code, out := tool("verify-policy", "--file", "non_existent_policy.yaml")
		wantCode(t, code, exitError, out)
		mustContain(t, out, "File not found: non_existent_policy.yaml")
	})
	t.Run("celVerifierTool_verifyPolicy_success", func(t *testing.T) {
		golden(t, true)
		path := writePolicy(t, "test_policy.yaml", "name: test_policy\n"+portPolicyHead+
			"    - id: port_check\n      assert:\n        - port == 80 || port != 80\n")
		code, out := tool("verify-policy", "--file", path, "--var", "port:int", "-fmt", "json")
		wantCode(t, code, exitVerified, out)
		mustContain(t, out, `"policyName": "test_policy.yaml"`, `"status": "VERIFIED"`)
	})
	t.Run("celVerifierTool_verifyPolicy_violated", func(t *testing.T) {
		golden(t, true)
		path := writePolicy(t, "violated_policy.yaml", "name: violated_policy\n"+portPolicyHead+
			"    - id: invalid_check\n      assert:\n        - port > 1024\n")
		code, out := tool("verify-policy", "--file", path, "--var", "port:int")
		wantCode(t, code, exitViolated, out)
	})
	t.Run("celVerifierTool_verifyPolicy_multipleInvariants_oneViolated", func(t *testing.T) {
		golden(t, true)
		path := writePolicy(t, "multi_invariant_policy.yaml", "name: multi_invariant_policy\n"+portPolicyHead+
			"    - id: valid_check\n      assert:\n        - port == 80 || port != 80\n"+
			"    - id: invalid_check\n      assert:\n        - port > 1024\n")
		code, out := tool("verify-policy", "--file", path, "--var", "port:int")
		wantCode(t, code, exitViolated, out)
		mustContain(t, out, "✓ Invariant 'valid_check': VERIFIED", "✗ Invariant 'invalid_check': VIOLATED")
	})
	t.Run("celVerifierTool_verifyPolicy_multipleInvariants_allVerified", func(t *testing.T) {
		golden(t, true)
		path := writePolicy(t, "multi_verified_policy.yaml", "name: multi_verified_policy\n"+portPolicyHead+
			"    - id: check_1\n      assert:\n        - port == 80 || port != 80\n"+
			"    - id: check_2\n      assert:\n        - port > 0 || port <= 0\n")
		code, out := tool("verify-policy", "--file", path, "--var", "port:int")
		wantCode(t, code, exitVerified, out)
	})
	t.Run("celVerifierTool_verifyPolicy_inconclusive", func(t *testing.T) {
		golden(t, true)
		path := writePolicy(t, "inconclusive_policy.yaml", "name: inconclusive_policy\n"+portPolicyHead+
			"    - id: approx_check\n      assert:\n        - int('123') == 123\n")
		code, out := tool("verify-policy", "--file", path, "--var", "port:int")
		wantCode(t, code, exitInconclusive, out)
	})
	t.Run("celVerifierTool_verifyPolicy_compilationError", func(t *testing.T) {
		requireZ3(t)
		path := writePolicy(t, "bad_policy.yaml", "name: bad\nrule:\n  match:\n    - output: 'true' +\n")
		code, out := tool("verify-policy", "--file", path)
		wantCode(t, code, exitError, out)
		mustContain(t, out, "Policy compilation error:")
	})
	t.Run("celVerifierTool_verifyPolicy_invalidInvariant", func(t *testing.T) {
		requireZ3(t)
		path := writePolicy(t, "bad_invariant.yaml", "name: bad\n"+portPolicyHead+
			"    - id: bad\n      assert:\n        - undeclared > 1\n")
		code, out := tool("verify-policy", "--file", path, "--var", "port:int")
		wantCode(t, code, exitError, out)
		mustContain(t, out, "Compilation error:", "undeclared")
	})
	t.Run("celVerifierTool_checkSat_verified", func(t *testing.T) {
		golden(t, false)
		code, out := tool("check-sat", "--expr", "x > 0", "--var", "x:int")
		wantCode(t, code, exitVerified, out)
	})
	t.Run("celVerifierTool_checkValid_violated", func(t *testing.T) {
		golden(t, false)
		code, out := tool("check-valid", "--expr", "x > 0", "--var", "x:int")
		wantCode(t, code, exitViolated, out)
	})
	t.Run("celVerifierTool_verifyEquiv_verified", func(t *testing.T) {
		golden(t, false)
		code, out := tool("verify-equiv", "--expr1", "x > 10", "--expr2", "10 < x", "--var", "x:int")
		wantCode(t, code, exitVerified, out)
	})
	t.Run("celVerifierTool_checkSat_compilationError", func(t *testing.T) {
		code, out := tool("check-sat", "--expr", "invalid + + syntax", "--var", "x:int")
		wantCode(t, code, exitError, out)
		mustContain(t, out, "Compilation error")
	})
	t.Run("celVerifierTool_checkValid_withUnknownOption_violated", func(t *testing.T) {
		golden(t, false)
		code, out := tool("check-valid", "--expr", "x == x", "--var", "x:int", "-u", "x")
		wantCode(t, code, exitViolated, out)
	})
	t.Run("celVerifierTool_checkValid_inconclusive", func(t *testing.T) {
		golden(t, false)
		code, out := tool("check-valid", "--expr", "int('123') == 123")
		wantCode(t, code, exitInconclusive, out)
	})
	t.Run("celVerifierTool_invalidOutputFormat_defaultsToText", func(t *testing.T) {
		golden(t, false)
		_, out := tool("check-sat", "--expr", "x > 0", "--var", "x:int", "-fmt", "invalid_fmt")
		mustContain(t, out, "Invalid output format 'invalid_fmt'. Defaulting to TEXT.", "[VERIFIED]")
	})
	t.Run("celVerifierTool_invalidVariable", func(t *testing.T) {
		code, out := tool("check-sat", "--expr", "x > 0", "--var", "x:foo_bar")
		wantCode(t, code, exitError, out)
		mustContain(t, out, "Verification error: Unsupported type for CLI variable declaration: 'foo_bar'.")
	})
	t.Run("celVerifierTool_missingRequiredOption", func(t *testing.T) {
		code, out := tool("check-sat", "--var", "x:int")
		wantCode(t, code, exitError, out)
		mustContain(t, out, "Missing required option: '--expr'")
	})
	t.Run("celVerifierTool_version", func(t *testing.T) {
		code, out := tool("--version")
		wantCode(t, code, 0, out)
		mustContain(t, out, "cel-verifier ")
	})
}

func TestCore(t *testing.T) {
	t.Run("checkSatisfiable_satisfiable", func(t *testing.T) {
		golden(t, false)
		r, err := checkSatisfiable("role == 'editor' && port > 1024", mustVars(t, "role:string", "port:int"), opts5s())
		if err != nil {
			t.Fatal(err)
		}
		if r.Status != verifier.Verified || !strings.Contains(r.Message(), "satisfiable") {
			t.Errorf("got %v %q", r.Status, r.Message())
		}
	})
	t.Run("checkValid_valid", func(t *testing.T) {
		golden(t, false)
		wantStatus(t, verifier.Verified)(checkValid("x > 10 || x <= 10", mustVars(t, "x:int"), opts5s()))
	})
	t.Run("verifyEquivalence_equivalent", func(t *testing.T) {
		golden(t, false)
		wantStatus(t, verifier.Verified)(verifyEquivalence("x > 10", "10 < x", mustVars(t, "x:int"), opts5s()))
	})
	t.Run("verifyEquivalence_canonicalizedMapComprehension", func(t *testing.T) {
		golden(t, false)
		wantStatus(t, verifier.Verified)(verifyEquivalence(
			"map_string_int.exists(k, v, k == 'foo' && v == 1)",
			"map_string_int.exists(k, v, v == 1 && k == 'foo')",
			mustVars(t, "map_string_int:map<string, int>"), opts5s()))
	})
	t.Run("verifyEquivalence_wellKnownTypesSupportedByDefault", func(t *testing.T) {
		golden(t, true)
		vars := mustVars(t, "x:int", "w:google.protobuf.Int64Value", "s:google.protobuf.Struct")
		for _, c := range [][2]string{
			{"google.protobuf.Struct{fields: {'a': google.protobuf.Value{number_value: 1.0}, ?'b': optional.none()}}", "{'a': 1.0}"},
			{"google.protobuf.ListValue{values: [google.protobuf.Value{string_value: 'x'}]}", "['x']"},
			{"google.protobuf.Int64Value{value: x} == x && google.protobuf.Int64Value{} == 0 && google.protobuf.StringValue{value: 'hi'} == 'hi'", "true"},
			{"google.protobuf.Timestamp{seconds: 100} == timestamp(100) && google.protobuf.Timestamp{seconds: 100, nanos: 500} > timestamp(100) && google.protobuf.Duration{seconds: 50} == timestamp(150) - timestamp(100)", "true"},
			{"w == null || w == google.protobuf.Int64Value{value: w}", "true"},
		} {
			wantStatus(t, verifier.Verified)(verifyEquivalence(c[0], c[1], vars, opts5s()))
		}
		results, err := verifyPolicyInvariants("name: wkt_policy\n"+
			"rule:\n  match:\n"+
			"    - condition: \"w == google.protobuf.Int64Value{value: 10}\"\n      output: 'true'\n"+
			"    - output: 'false'\n"+
			"verification:\n  invariants:\n    - id: wkt_check\n      assert:\n"+
			"        - \"w != 10 || w == google.protobuf.Int64Value{value: 10}\"\n", vars, opts5s())
		if err != nil {
			t.Fatal(err)
		}
		if len(results) != 1 || results[0].id != "wkt_check" || results[0].result.Status != verifier.Verified {
			t.Errorf("got %+v", results)
		}
	})
	t.Run("verifyPolicyInvariants_success", func(t *testing.T) {
		golden(t, true)
		results, err := verifyPolicyInvariants("name: secure_access_policy\n"+portPolicyHead+
			"    - id: port_check\n      assert:\n        - port == 80 || port != 80\n", mustVars(t, "port:int"), opts5s())
		if err != nil {
			t.Fatal(err)
		}
		if len(results) != 1 || results[0].id != "port_check" || results[0].result.Status != verifier.Verified {
			t.Errorf("got %+v", results)
		}
	})
	t.Run("verifyPolicyEquivalence_equivalent", func(t *testing.T) {
		golden(t, true)
		a := "name: policy_a\nrule:\n  match:\n    - condition: port == 80\n      output: 'true'\n    - output: 'false'\n"
		b := "name: policy_b\nrule:\n  match:\n    - condition: 80 == port\n      output: 'true'\n    - output: 'false'\n"
		wantStatus(t, verifier.Verified)(verifyPolicyEquivalence(a, b, mustVars(t, "port:int"), opts5s()))
	})
}

func wantStatus(t *testing.T, want verifier.Status) func(verifier.Result, error) {
	t.Helper()
	return func(r verifier.Result, err error) {
		t.Helper()
		if err != nil {
			t.Fatal(err)
		}
		if r.Status != want {
			t.Errorf("status = %v, want %v: %s", r.Status, want, r.Message())
		}
	}
}

func TestFormat(t *testing.T) {
	verified := verifier.Result{Status: verifier.Verified, Reason: "Condition is satisfiable."}
	violated := verifier.Result{Status: verifier.Violated, Reason: "Condition is not always true.", Counterexample: " Counterexample input:\n  x = 0"}
	inconclusive := verifier.Result{Status: verifier.Inconclusive, Reason: "Inconclusive: calls to `int`."}

	t.Run("formatTextResults_verified", func(t *testing.T) {
		want := ansiGreen + ansiBold + "[VERIFIED]" + ansiReset + " Condition is satisfiable."
		if got := formatTextResult(verified); got != want {
			t.Errorf("got %q, want %q", got, want)
		}
	})
	t.Run("formatTextPolicyResults_verifiedAndViolated", func(t *testing.T) {
		text := formatTextPolicyResults("test_policy", []namedResult{{"inv_1", verified}, {"inv_2", violated}})
		mustContain(t, text, "Policy Invariant Verification for 'test_policy':",
			"✓ Invariant 'inv_1': VERIFIED", "✗ Invariant 'inv_2': VIOLATED", "\n      x = 0")
	})
	t.Run("formatTextPolicyResults_inconclusive", func(t *testing.T) {
		mustContain(t, formatTextPolicyResults("test_policy", []namedResult{{"inv_1", inconclusive}}),
			"Invariant 'inv_1': INCONCLUSIVE")
	})
	t.Run("formatJsonResult", func(t *testing.T) {
		want := "{\n  \"status\": \"VIOLATED\",\n  \"message\": \"Condition is not always true. Counterexample input:\\n  x = 0\"\n}"
		if got := formatJSONResult(violated); got != want {
			t.Errorf("got %q, want %q", got, want)
		}
	})
	t.Run("formatJsonPolicyResults_multipleInvariants", func(t *testing.T) {
		got := formatJSONPolicyResults("my_policy", []namedResult{{"inv_1", verified}, {"inv_2", violated}})
		want := "{\n  \"policyName\": \"my_policy\",\n  \"invariants\": [\n" +
			"    {\n      \"id\": \"inv_1\",\n      \"status\": \"VERIFIED\",\n      \"message\": \"Condition is satisfiable.\"\n    },\n" +
			"    {\n      \"id\": \"inv_2\",\n      \"status\": \"VIOLATED\",\n      \"message\": \"Condition is not always true. Counterexample input:\\n  x = 0\"\n    }\n" +
			"  ]\n}"
		if got != want {
			t.Errorf("got\n%s\nwant\n%s", got, want)
		}
	})
	t.Run("formatJson_escapesSpecialCharacters", func(t *testing.T) {
		json := formatJSONPolicyResults("policy_with_\"quote\"\nand_newline", []namedResult{{"inv\ttab\x01", inconclusive}})
		mustContain(t, json, `policy_with_\"quote\"\nand_newline`, `inv\ttab\u0001`)
	})
}

func TestParseVariables(t *testing.T) {
	typeOf := func(vs []variable, name string) *cel.Type {
		for _, v := range vs {
			if v.name == name {
				return v.typ
			}
		}
		return nil
	}
	check := func(t *testing.T, specs []string, want map[string]*cel.Type) {
		t.Helper()
		vs := mustVars(t, specs...)
		for name, w := range want {
			if got := typeOf(vs, name); got == nil || !got.IsExactType(w) || got.String() != w.String() {
				t.Errorf("%s: got %v, want %v", name, got, w)
			}
		}
	}
	t.Run("success", func(t *testing.T) {
		check(t, []string{"x:int", "role:string", "is_admin:bool", "tags:list<string>", "scores:map<string, int>",
			"created_at:timestamp", "timeout:duration", "opt_user:optional<string>"},
			map[string]*cel.Type{
				"x": cel.IntType, "role": cel.StringType, "is_admin": cel.BoolType, "tags": cel.ListType(cel.StringType),
				"scores": cel.MapType(cel.StringType, cel.IntType), "created_at": cel.TimestampType,
				"timeout": cel.DurationType, "opt_user": cel.OptionalType(cel.StringType),
			})
	})
	t.Run("allTypesIncludingDyn", func(t *testing.T) {
		check(t, []string{"u:uint", "d:double", "fl:float", "b:bytes", "dyn_val:dyn", "flag:boolean",
			"t:google.protobuf.timestamp", "dur:google.protobuf.duration", "opt:optional_type<int>",
			"nested_list:list<dyn>", "nested_map:map<string, dyn>", "w:google.protobuf.Int64Value",
			"s:google.protobuf.Struct", "lv:google.protobuf.ListValue", "v:google.protobuf.Value"},
			map[string]*cel.Type{
				"u": cel.UintType, "d": cel.DoubleType, "fl": cel.DoubleType, "b": cel.BytesType, "dyn_val": cel.DynType,
				"flag": cel.BoolType, "t": cel.TimestampType, "dur": cel.DurationType, "opt": cel.OptionalType(cel.IntType),
				"nested_list": cel.ListType(cel.DynType), "nested_map": cel.MapType(cel.StringType, cel.DynType),
				"w": cel.NullableType(cel.IntType), "s": cel.MapType(cel.StringType, cel.DynType),
				"lv": cel.ListType(cel.DynType), "v": cel.DynType,
			})
	})
	t.Run("nestedTypes", func(t *testing.T) {
		check(t, []string{"nested_map:map<string, map<string, int>>", "nested_list_map:map<string, list<int>>"},
			map[string]*cel.Type{
				"nested_map":      cel.MapType(cel.StringType, cel.MapType(cel.StringType, cel.IntType)),
				"nested_list_map": cel.MapType(cel.StringType, cel.ListType(cel.IntType)),
			})
	})
	t.Run("errors", func(t *testing.T) {
		for spec, want := range map[string]string{
			"x_no_colon":    "Expected format 'name:type'",
			"x:foo_bar":     "Supported types: int, uint, string, bool, double, bytes, dyn, timestamp, duration, list<T>, map<K, V>, optional<T>.",
			"x:map<string>": "Invalid map type format",
			"":              "Expected format 'name:type'",
			"   ":           "Expected format 'name:type'",
			":int":          "Variable name cannot be empty",
		} {
			_, err := parseVariables([]string{spec})
			if err == nil || !strings.Contains(err.Error(), want) {
				t.Errorf("parseVariables(%q) = %v, want an error containing %q", spec, err, want)
			}
		}
	})
	t.Run("empty", func(t *testing.T) {
		if vs, err := parseVariables(nil); err != nil || len(vs) != 0 {
			t.Errorf("got %v, %v", vs, err)
		}
	})
}
