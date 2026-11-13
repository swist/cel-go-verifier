package z3proc

import (
	"testing"
	"time"

	"github.com/swist/cel-go-verifier/smt"
)

func newBackend(t *testing.T) *Backend {
	b := New()
	if !b.Available() {
		t.Skip("z3 not available; set Z3_PATH")
	}
	return b
}

func TestRoundTrip(t *testing.T) {
	b := newBackend(t)
	c := smt.NewContext(b)
	defer b.Close(c)
	listRef := c.MkUninterpretedSort("ListRef")
	cel := c.MkDatatypeSort("CelValue", []smt.ConstructorSpec{
		{Name: "Bool", TesterName: "isBool", FieldNames: []string{"getBool"}, FieldSorts: []*smt.Sort{c.BoolSort()}},
		{Name: "Int", TesterName: "isInt", FieldNames: []string{"getInt"}, FieldSorts: []*smt.Sort{c.IntSort()}},
		{Name: "CelError", TesterName: "isError"},
		{Name: "List", TesterName: "isList", FieldNames: []string{"getListRef"}, FieldSorts: []*smt.Sort{listRef}},
	})
	asSeq := c.MkFuncDecl("as_seq", []*smt.Sort{listRef}, c.SeqSort(cel))
	x := c.MkConst("x", cel)
	k := cel.Datatype.Constructors
	isList := c.MkApp(k[3].Tester, x)
	seq := c.MkApp(asSeq, c.MkApp(k[3].Accessors[0], x))
	s, err := b.NewSolver(c, 5*time.Second)
	if err != nil {
		t.Fatal(err)
	}
	defer s.Close()
	s.Assert(isList, c.MkEq(c.MkLength(seq), c.MkInt(2)), c.MkEq(c.MkNth(seq, c.MkInt(0)), c.MkApp(k[1].Decl, c.MkInt(-7))))
	st, err := s.Check()
	if err != nil || st != smt.Sat {
		t.Fatalf("check = %v, %v", st, err)
	}
	m := s.Model()
	v, err := m.Eval(x, true)
	if err != nil {
		t.Fatal(err)
	}
	if v.Op != smt.OpApp || v.Decl != k[3].Decl || v.Args[0].Op != smt.OpModelValue {
		t.Fatalf("x = %s", v)
	}
	// Model values can be used in new terms.
	n, err := m.Eval(c.MkLength(c.MkApp(asSeq, v.Args[0])), true)
	if err != nil {
		t.Fatal(err)
	}
	if n.Op != smt.OpIntLit || n.Int.Int64() != 2 {
		t.Fatalf("len = %s", n)
	}
	e, err := m.Eval(c.MkNth(c.MkApp(asSeq, v.Args[0]), c.MkInt(0)), true)
	if err != nil {
		t.Fatal(err)
	}
	if e != c.MkApp(k[1].Decl, c.MkInt(-7)) {
		t.Fatalf("elem = %s", e)
	}
	// Simplification.
	if got := c.Simplify(c.MkApp(k[1].Tester, c.MkApp(k[1].Decl, c.MkInt(3)))); !got.IsTrue() {
		t.Fatalf("simplify tester = %s", got)
	}
	d := c.MkFP(0.1, c.FPSortDouble())
	if got := c.Simplify(c.MkFPIsZero(d)); !got.IsFalse() {
		t.Fatalf("simplify isZero = %s", got)
	}
	if got := c.Simplify(c.MkAdd(c.MkInt(2), c.MkInt(3))); got != c.MkInt(5) {
		t.Fatalf("simplify add = %s", got)
	}
	fresh := c.MkFreshConst("!listRef_", listRef)
	if got := smt.Print(c.MkEq(fresh, fresh)); got != "(= !listRef_!0 !listRef_!0)" {
		t.Fatalf("print = %s", got)
	}
	weird := c.MkConst("!fn_a|b", cel)
	if got := c.Simplify(c.MkEq(weird, weird)); !got.IsTrue() {
		t.Fatalf("simplify weird = %s", got)
	}
}
