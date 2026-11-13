package verifier_test

import (
	"compress/gzip"
	"encoding/json"
	"flag"
	"io"
	"os"
	"path/filepath"
	"regexp"
	"strings"
	"sync"
	"testing"
	"time"

	"cel.dev/cel-go/cel"
	"cel.dev/cel-go/common"
	"cel.dev/cel-go/common/ast"
	"cel.dev/cel-go/common/operators"
	"cel.dev/cel-go/common/types"
	"cel.dev/cel-go/ext"
	"cel.dev/cel-go/parser"
	proto3pb "cel.dev/expr/conformance/proto3"

	"github.com/swist/cel-go-verifier/internal/smtdiff"
	"github.com/swist/cel-go-verifier/smt"
	"github.com/swist/cel-go-verifier/smt/z3proc"
	"github.com/swist/cel-go-verifier/verifier"
)

// The tests in this file are ports of cel-java's CelVerifierZ3ImplTest. Each
// case runs the same verification as the Java test, checks the same outcome,
// and compares the solver transcript with the one cel-java produced
// (testdata/golden/java, written by javaref).

var dumpDir = flag.String("dump_transcripts", "", "directory to write the Go solver transcripts to")

var strictGolden = flag.Bool("strict_golden", true, "fail tests whose solver transcript differs from cel-java's")

const goldenDir = "../testdata/golden/java"

// testBackend creates the solver backend of the tests: the z3 executable, or
// libz3 when built with -tags z3cgo.
var (
	testBackend = func() smt.Backend { return z3proc.New() }
	cgoBackend  = false
)

func requireZ3(t testing.TB) {
	t.Helper()
	if !cgoBackend && !z3proc.New().Available() {
		t.Skip("z3 not found; set Z3_PATH")
	}
}

// firstElemMacro mirrors the Java test's custom first_elem receiver macro.
var firstElemMacro = parser.NewReceiverMacro("first_elem", 0,
	func(eh parser.ExprHelper, target ast.Expr, args []ast.Expr) (ast.Expr, *common.Error) {
		return eh.NewComprehension(target, "x", "accu",
			eh.NewLiteral(types.Int(-1)),
			eh.NewCall(operators.Equals, eh.NewAccuIdent(), eh.NewLiteral(types.Int(-1))),
			eh.NewIdent("x"),
			eh.NewAccuIdent()), nil
	})

var (
	envOnce sync.Once
	envVal  *cel.Env
)

// javaTestEnv mirrors CelVerifierZ3ImplTest.CEL.
func javaTestEnv(t testing.TB) *cel.Env {
	envOnce.Do(func() {
		var err error
		envVal, err = cel.NewEnv(
			cel.Container("cel.expr.conformance.proto3"),
			cel.Types(&proto3pb.TestAllTypes{}, &proto3pb.TestAllTypes_NestedMessage{}),
			ext.Bindings(), cel.OptionalTypes(), ext.TwoVarComprehensions(),
			cel.CrossTypeNumericComparisons(true),
			cel.Macros(cel.StandardMacros...),
			cel.Macros(firstElemMacro),
			cel.Variable("x", cel.IntType),
			cel.Variable("u", cel.UintType),
			cel.Variable("u1", cel.UintType),
			cel.Variable("u2", cel.UintType),
			cel.Variable("d", cel.DoubleType),
			cel.Variable("by", cel.BytesType),
			cel.Variable("y", cel.IntType),
			cel.Variable("a", cel.BoolType),
			cel.Variable("b", cel.BoolType),
			cel.Variable("role", cel.StringType),
			cel.Variable("country", cel.StringType),
			cel.Variable("string_var", cel.StringType),
			cel.Variable("port", cel.IntType),
			cel.Variable("dur", cel.DurationType),
			cel.Variable("ts", cel.TimestampType),
			cel.Variable("request", cel.DynType),
			cel.Variable("unknown_var", cel.DynType),
			cel.Variable("int_list", cel.ListType(cel.IntType)),
			cel.Variable("int_list_2", cel.ListType(cel.IntType)),
			cel.Variable("nested_list", cel.ListType(cel.ListType(cel.IntType))),
			cel.Variable("nested_list_2", cel.ListType(cel.ListType(cel.IntType))),
			cel.Variable("dyn_list", cel.ListType(cel.DynType)),
			cel.Variable("dyn_map", cel.MapType(cel.DynType, cel.DynType)),
			cel.Variable("dyn_int_map", cel.MapType(cel.DynType, cel.IntType)),
			cel.Variable("string_dyn_map", cel.MapType(cel.StringType, cel.DynType)),
			cel.Variable("dyn_var", cel.DynType),
			cel.Variable("dyn_var2", cel.DynType),
			cel.Variable("opt_var", cel.OptionalType(cel.IntType)),
			cel.Variable("opt_dyn_var", cel.OptionalType(cel.DynType)),
			cel.Variable("nullable_int", types.NewNullableType(types.IntType)),
			cel.Variable("string_int_map", cel.MapType(cel.StringType, cel.IntType)),
			cel.Variable("bytes_val", cel.BytesType),
			cel.Variable("string_int_list_map", cel.MapType(cel.StringType, cel.ListType(cel.IntType))),
			cel.Variable("test_all_types", cel.ObjectType("cel.expr.conformance.proto3.TestAllTypes")),
			cel.Variable("json_val", cel.ObjectType("google.protobuf.Value")),
			cel.Variable("json_list", cel.ObjectType("google.protobuf.ListValue")),
			cel.Variable("json_struct", cel.ObjectType("google.protobuf.Struct")),
		)
		if err != nil {
			panic(err)
		}
	})
	return envVal
}

// testTypeProvider lists the message types in the order cel-java's type
// provider for the same environment does (dumped by javaref).
type testTypeProvider struct {
	env  *cel.Env
	java string
}

func (p testTypeProvider) StructTypeNames() []string {
	testCases(nil, "")
	var out []string
	for _, n := range javaTypeOrder[p.java] {
		if t, ok := p.env.CELTypeProvider().FindStructType(n); ok && t.Parameters()[0].Kind() == types.StructKind {
			out = append(out, n)
		}
	}
	return out
}

func (p testTypeProvider) FieldType(msg, field string) (verifier.FieldInfo, bool) {
	return verifier.NewProtoTypeProvider(p.env.CELTypeProvider(),
		proto3pb.File_cel_expr_conformance_proto3_test_all_types_proto).FieldType(msg, field)
}

func compile(t testing.TB, env *cel.Env, expr string) *cel.Ast {
	t.Helper()
	a, iss := env.Compile(expr)
	if iss.Err() != nil {
		t.Fatalf("compile %q: %v", expr, iss.Err())
	}
	return a
}

// goldenRun runs f with a recording verifier and compares the transcript with cel-java's.
type goldenRun struct {
	t    *testing.T
	rec  *smtdiff.Recorder
	name string
}

func newGoldenRun(t *testing.T, name string) *goldenRun {
	requireZ3(t)
	return &goldenRun{t: t, rec: &smtdiff.Recorder{}, name: name}
}

func (g *goldenRun) verifier(opts ...verifier.Option) *verifier.Verifier {
	env := javaTestEnv(g.t)
	opts = append([]verifier.Option{
		verifier.Types(testTypeProvider{env, "types:CelVerifierZ3ImplTest.CEL"}),
		verifier.Recorder(g.rec.Factory()),
		verifier.Backend(testBackend()),
	}, opts...)
	v, err := verifier.New(env, opts...)
	if err != nil {
		g.t.Fatal(err)
	}
	return v
}

// knownDivergences are the cases whose transcripts differ from cel-java's
// because cel-go's environment differs, not because the verifier does.
var knownDivergences = map[string]string{
	z3 + "isSatisfiable_failure[DYN_OPTIONAL_VALUE_OUT_OF_RANGE]":                      "cel-go's checker types dyn_var.value() as int and resolves `< 0u` to less_int64_uint64 only",
	z3 + "isAlwaysTrue_success[TYPE_AXIOM_OPTIONAL]":                                   "cel-go's checker types the optional_type identifier as type(optional_type(dyn)), cel-java as type(optional_type(int))",
	z3 + "isAlwaysTrue_violation_returnsFalse[UNINTERPRETED_CONVERSION_CAN_ERROR_INT]": "cel-go's stdlib has int(duration), which cel-java's lacks",
}

// procDivergences differ only with the z3 process backend: Z3's simplifier
// orders arguments by term creation, which only the cgo backend reproduces.
var procDivergences = map[string]string{
	z3 + "isAlwaysTrue_success[MAP_LITERAL_SINGLE_VARIABLE_KEY_LIST_VALUE]":              "simplifier argument order",
	z3 + "isAlwaysTrue_success[MAP_LITERAL_WITH_VARIABLE_KEY_EQ]":                        "simplifier argument order",
	z3 + "isAlwaysTrue_violation_returnsFalse[OPTIONAL_MAP_ENTRY_DYN_VAR_TYPE_MISMATCH]": "simplifier argument order",
}

var goldenStats struct {
	sync.Mutex
	matched, mismatched, missing int
}

func (g *goldenRun) check() {
	t := g.t
	t.Helper()
	if *dumpDir != "" {
		_ = os.WriteFile(filepath.Join(*dumpDir, g.name+".smt2"), []byte(g.rec.String()), 0o644)
	}
	path := filepath.Join(goldenDir, g.name+".smt2.gz")
	f, err := os.Open(path)
	if err != nil {
		goldenStats.Lock()
		goldenStats.missing++
		goldenStats.Unlock()
		t.Logf("no golden %s", path)
		return
	}
	defer f.Close()
	zr, err := gzip.NewReader(f)
	if err != nil {
		t.Fatal(err)
	}
	want, err := io.ReadAll(zr)
	if err != nil {
		t.Fatal(err)
	}
	c := smtdiff.New()
	wq, err := c.Parse(string(want))
	if err != nil {
		t.Fatalf("parsing golden: %v", err)
	}
	gq, err := c.Parse(g.rec.String())
	if err != nil {
		t.Fatalf("parsing transcript: %v", err)
	}
	if d := c.Diff(wq, gq); d != "" {
		if *dumpDir != "" {
			if w, gt, ok := c.FirstDiff(wq, gq); ok {
				_ = os.WriteFile(filepath.Join(*dumpDir, g.name+".want.txt"), []byte(c.RenderPretty(w)), 0o644)
				_ = os.WriteFile(filepath.Join(*dumpDir, g.name+".got.txt"), []byte(c.RenderPretty(gt)), 0o644)
			}
		}
		goldenStats.Lock()
		goldenStats.mismatched++
		goldenStats.Unlock()
		reason, known := knownDivergences[g.name]
		if !known && !cgoBackend {
			reason, known = procDivergences[g.name]
		}
		if known {
			t.Logf("transcript differs from cel-java as expected (%s): %s", reason, d)
			return
		}
		if *strictGolden {
			t.Errorf("transcript differs from cel-java (%s): %s", path, d)
		} else {
			t.Logf("transcript differs from cel-java (%s): %s", path, d)
		}
		return
	}
	goldenStats.Lock()
	goldenStats.matched++
	goldenStats.Unlock()
}

func TestMain(m *testing.M) {
	flag.Parse()
	code := m.Run()
	if goldenStats.matched+goldenStats.mismatched+goldenStats.missing > 0 {
		println("golden transcripts: matched", goldenStats.matched, "mismatched", goldenStats.mismatched, "missing", goldenStats.missing)
	}
	os.Exit(code)
}

// testCases loads a parameterized test case table dumped from cel-java.
func testCases(t testing.TB, enum string) []map[string]any {
	casesOnce.Do(func() {
		b, err := os.ReadFile("../testdata/golden/testcases.json")
		if err != nil {
			panic(err)
		}
		var raw map[string]json.RawMessage
		if err := json.Unmarshal(b, &raw); err != nil {
			panic(err)
		}
		allCases = map[string][]map[string]any{}
		javaTypeOrder = map[string][]string{}
		for k, v := range raw {
			if strings.HasPrefix(k, "types:") {
				var names []string
				_ = json.Unmarshal(v, &names)
				javaTypeOrder[k] = names
				continue
			}
			var cs []map[string]any
			if err := json.Unmarshal(v, &cs); err != nil {
				panic(err)
			}
			allCases[k] = cs
		}
	})
	if t == nil {
		return nil
	}
	t.Helper()
	cs, ok := allCases[enum]
	if !ok {
		t.Fatalf("no test cases %s", enum)
	}
	return cs
}

var (
	casesOnce     sync.Once
	allCases      map[string][]map[string]any
	javaTypeOrder map[string][]string
)

func str(c map[string]any, k string) string { s, _ := c[k].(string); return s }

func strs(c map[string]any, k string) []string {
	var out []string
	for _, v := range c[k].([]any) {
		out = append(out, v.(string))
	}
	return out
}

func expectStatus(t *testing.T, r verifier.Result, want verifier.Status) {
	t.Helper()
	if r.Status != want {
		t.Errorf("status = %v, want %v; message: %s", r.Status, want, r.Message())
	}
}

func expectFragments(t *testing.T, r verifier.Result, fragments []string) {
	t.Helper()
	for _, f := range fragments {
		if !javaContainsMatch(f, r.Message()) {
			t.Errorf("message %q doesn't match %q", r.Message(), f)
		}
	}
}

// javaContainsMatch is Truth's containsMatch: a Java regex search. RE2 lacks
// lookahead, so a trailing negative lookahead (?!...) is checked by hand.
func javaContainsMatch(pattern, s string) bool {
	if i := strings.Index(pattern, "(?!"); i >= 0 && strings.HasSuffix(pattern, ")") {
		prefix := regexp.MustCompile(pattern[:i])
		not := regexp.MustCompile("^(?:" + pattern[i+3:len(pattern)-1] + ")")
		for _, m := range prefix.FindAllStringIndex(s, -1) {
			if !not.MatchString(s[m[1]:]) {
				return true
			}
		}
		return false
	}
	return regexp.MustCompile(pattern).MatchString(s)
}

const z3 = "CelVerifierZ3ImplTest."

// runTable runs fn for each case of a table, as subtests named like the Java parameterized tests.
func runTable(t *testing.T, enum, method string, fn func(t *testing.T, g *goldenRun, c map[string]any)) {
	for _, c := range testCases(t, z3[:len(z3)-1]+"."+enum) {
		c := c
		name := str(c, "name")
		t.Run(name, func(t *testing.T) {
			t.Parallel()
			g := newGoldenRun(t, z3+method+"["+name+"]")
			fn(t, g, c)
			g.check()
		})
	}
}

func TestIsSatisfiableSuccess(t *testing.T) {
	runTable(t, "IsSatisfiableTestCase", "isSatisfiable_success", func(t *testing.T, g *goldenRun, c map[string]any) {
		r, err := g.verifier().IsSatisfiable(compile(t, javaTestEnv(t), str(c, "expr")))
		if err != nil {
			t.Fatal(err)
		}
		expectStatus(t, r, verifier.Verified)
		expectFragments(t, r, strs(c, "expectedFragments"))
	})
}

func TestIsSatisfiableInconclusive(t *testing.T) {
	runTable(t, "IsSatisfiableInconclusiveTestCase", "isSatisfiable_inconclusive", func(t *testing.T, g *goldenRun, c map[string]any) {
		r, err := g.verifier().IsSatisfiable(compile(t, javaTestEnv(t), str(c, "expr")))
		if err != nil {
			t.Fatal(err)
		}
		expectStatus(t, r, verifier.Inconclusive)
	})
}

func TestIsSatisfiableFailure(t *testing.T) {
	runTable(t, "IsUnsatisfiableTestCase", "isSatisfiable_failure", func(t *testing.T, g *goldenRun, c map[string]any) {
		r, err := g.verifier().IsSatisfiable(compile(t, javaTestEnv(t), str(c, "expr")))
		if err != nil {
			t.Fatal(err)
		}
		expectStatus(t, r, verifier.Violated)
	})
}

func TestIsAlwaysTrueSuccess(t *testing.T) {
	runTable(t, "IsAlwaysTrueTestCase", "isAlwaysTrue_success", func(t *testing.T, g *goldenRun, c map[string]any) {
		r, err := g.verifier().IsAlwaysTrue(compile(t, javaTestEnv(t), str(c, "expr")))
		if err != nil {
			t.Fatal(err)
		}
		expectStatus(t, r, verifier.Verified)
	})
}

func TestIsAlwaysTrueViolation(t *testing.T) {
	runTable(t, "IsAlwaysTrueViolationTestCase", "isAlwaysTrue_violation_returnsFalse", func(t *testing.T, g *goldenRun, c map[string]any) {
		r, err := g.verifier().IsAlwaysTrue(compile(t, javaTestEnv(t), str(c, "expr")))
		if err != nil {
			t.Fatal(err)
		}
		expectStatus(t, r, verifier.Violated)
		expectFragments(t, r, strs(c, "expectedFragments"))
	})
}

func TestIsAlwaysTrueInconclusive(t *testing.T) {
	runTable(t, "IsInconclusiveTestCase", "isAlwaysTrue_inconclusive", func(t *testing.T, g *goldenRun, c map[string]any) {
		r, err := g.verifier().IsAlwaysTrue(compile(t, javaTestEnv(t), str(c, "expr")))
		if err != nil {
			t.Fatal(err)
		}
		expectStatus(t, r, verifier.Inconclusive)
	})
}

func TestVerifyEquivalenceSuccess(t *testing.T) {
	runTable(t, "EquivalenceTestCase", "verifyEquivalence_success", func(t *testing.T, g *goldenRun, c map[string]any) {
		env := javaTestEnv(t)
		r, err := g.verifier().VerifyEquivalence(compile(t, env, str(c, "exprA")), compile(t, env, str(c, "exprB")))
		if err != nil {
			t.Fatal(err)
		}
		expectStatus(t, r, verifier.Verified)
	})
}

func TestVerifyEquivalenceViolation(t *testing.T) {
	runTable(t, "EquivalenceViolationTestCase", "verifyEquivalence_violation_returnsFalse", func(t *testing.T, g *goldenRun, c map[string]any) {
		env := javaTestEnv(t)
		r, err := g.verifier().VerifyEquivalence(compile(t, env, str(c, "exprA")), compile(t, env, str(c, "exprB")))
		if err != nil {
			t.Fatal(err)
		}
		expectStatus(t, r, verifier.Violated)
	})
}

func TestVerifyEquivalenceInconclusive(t *testing.T) {
	runTable(t, "EquivalenceInconclusiveTestCase", "verifyEquivalence_inconclusive", func(t *testing.T, g *goldenRun, c map[string]any) {
		env := javaTestEnv(t)
		r, err := g.verifier().VerifyEquivalence(compile(t, env, str(c, "exprA")), compile(t, env, str(c, "exprB")))
		if err != nil {
			t.Fatal(err)
		}
		expectStatus(t, r, verifier.Inconclusive)
	})
}

func TestVerifyImplicationVerified(t *testing.T) {
	runTable(t, "HoldingImplicationTestCase", "verifyImplication_verified", func(t *testing.T, g *goldenRun, c map[string]any) {
		env := javaTestEnv(t)
		r, err := g.verifier().VerifyImplication(compile(t, env, str(c, "assume")), compile(t, env, str(c, "assertion")), nil, "Implication")
		if err != nil {
			t.Fatal(err)
		}
		expectStatus(t, r, verifier.Verified)
	})
}

var _ = strings.Contains
var _ = time.Second
