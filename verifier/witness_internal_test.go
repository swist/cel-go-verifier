package verifier

import (
	"strings"
	"testing"
	"time"

	"cel.dev/cel-go/cel"

	"github.com/swist/cel-go-verifier/smt"
	"github.com/swist/cel-go-verifier/smt/z3proc"
)

// Port of CelVerifierZ3ImplTest.generateWitness_mapWithoutExactValue_valueEmpty:
// a map whose key sequence and presence disagree has no exact runtime value.
func TestGenerateWitnessMapWithoutExactValueValueEmpty(t *testing.T) {
	b := z3proc.New()
	if !b.Available() {
		t.Skip("z3 not found; set Z3_PATH")
	}
	for name, tc := range map[string]struct{ keys, present []string }{
		"DUPLICATE_KEY":               {[]string{"a", "a"}, []string{"a"}},
		"ABSENT_KEY":                  {[]string{"a", "b"}, []string{"a"}},
		"PRESENT_KEY_NOT_IN_SEQUENCE": {nil, []string{"a"}},
		"PAST_UNROLL_LIMIT":           {[]string{"a", "b", "c", "d", "e", "f"}, []string{"a", "b", "c", "d", "e", "f"}},
	} {
		t.Run(name, func(t *testing.T) {
			c := smt.NewContext(b)
			defer b.Close(c)
			ts := NewTypeSystem(c, false)
			m := c.MkConst("map", ts.CelValueSort())
			ref := ts.GetMapRef(m)
			keys := c.MkEmptySeq(c.SeqSort(ts.CelValueSort()))
			for _, k := range tc.keys {
				keys = c.MkConcat(keys, c.MkUnit(ts.MkString(k)))
			}
			presence := c.MkConstArray(ts.CelValueSort(), c.MkFalse())
			for _, k := range tc.present {
				presence = c.MkStore(presence, ts.MkString(k), c.MkTrue())
			}
			s, err := b.NewSolver(c, 10*time.Second)
			if err != nil {
				t.Fatal(err)
			}
			defer s.Close()
			s.Assert(ts.IsMap(m), c.MkEq(ts.GetMapKeys(ref), keys), c.MkEq(ts.GetMapPresence(ref), presence))
			if st, err := s.Check(); err != nil || st != smt.Sat {
				t.Fatalf("check = %v, %v", st, err)
			}
			w, err := generateWitness(ts, s.Model(), 5, []*smt.Term{m})
			if err != nil {
				t.Fatal(err)
			}
			if v := w.Variables["map"]; v.Value != nil {
				t.Errorf("value = %v, want none (display %s)", v.Value, v.Display)
			}
		})
	}
}

// Ports of getNumericEqualityWithConstant_skipsIntForDouble and _skipsDoubleForInt.
func TestNumericEqualityWithConstantSkipsOtherKinds(t *testing.T) {
	b := z3proc.New()
	if !b.Available() {
		t.Skip("z3 not found; set Z3_PATH")
	}
	env, err := cel.NewEnv(cel.Variable("d", cel.DoubleType), cel.Variable("x", cel.IntType))
	if err != nil {
		t.Fatal(err)
	}
	for expr, want := range map[string]struct{ has, hasNot []string }{
		"d == 5.0": {[]string{"getDouble"}, []string{"getInt", "getUint"}},
		"x == 5":   {[]string{"getInt"}, nil},
	} {
		a, iss := env.Compile(expr)
		if iss.Err() != nil {
			t.Fatal(iss.Err())
		}
		c := smt.NewContext(b)
		r, _ := newFunctionRegistry(nil)
		tr := newASTTranslator(c, 3, nil, r, emptyTypeProvider{}, false)
		got := smt.Print(tr.translate(a.NativeRep()).z3)
		b.Close(c)
		for _, s := range want.has {
			if !strings.Contains(got, s) {
				t.Errorf("%s: %s doesn't contain %s", expr, got, s)
			}
		}
		for _, s := range want.hasNot {
			if strings.Contains(got, s) {
				t.Errorf("%s: %s contains %s", expr, got, s)
			}
		}
	}
}
