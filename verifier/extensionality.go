package verifier

import "github.com/swist/cel-go-verifier/smt"

// Extensionality axioms for the reference sorts. Without them the solver
// compares references by identity, so equal but distinctly built collections
// (e.g. [[1]] == [[1]]) would differ. Each reference r gets the ground axiom
// f(contents(r)) = r, from which congruence closure derives
// contents(r1) = contents(r2) => r1 = r2.

const (
	funcMkListRef = "!mkListRef"
	funcMkMapRef  = "!mkMapRef"
	funcMkMsgRef  = "!mkMsgRef"
)

func extensionalityAxioms(ts *TypeSystem, listRefs, mapRefs, msgRefs []*smt.Term) []*smt.Term {
	c := ts.c
	var axioms []*smt.Term
	if len(listRefs) > 0 {
		mk := ts.InternFuncDecl(funcMkListRef, []*smt.Sort{c.SeqSort(ts.celValueSort)}, ts.listRefSort)
		for _, ref := range listRefs {
			if isAppNamed(ref, funcMkListRef) {
				continue
			}
			ax := c.MkEq(c.MkApp(mk, ts.GetSeq(ref)), ref)
			if ref.IsAppOf(ts.listCons.Accessors[0]) {
				ax = c.MkImplies(ts.IsList(ref.Args[0]), ax)
			}
			axioms = append(axioms, ax)
		}
	}
	if len(mapRefs) > 0 {
		valuesSort := c.ArraySort(ts.celValueSort, ts.celValueSort)
		presenceSort := c.ArraySort(ts.celValueSort, c.BoolSort())
		mk := ts.InternFuncDecl(funcMkMapRef, []*smt.Sort{valuesSort, presenceSort}, ts.mapRefSort)
		for _, ref := range mapRefs {
			if isAppNamed(ref, funcMkMapRef) {
				continue
			}
			ax := c.MkEq(c.MkApp(mk, ts.GetMapValues(ref), ts.GetMapPresence(ref)), ref)
			if ref.IsAppOf(ts.mapCons.Accessors[0]) {
				ax = c.MkImplies(ts.IsMap(ref.Args[0]), ax)
			}
			axioms = append(axioms, ax)
		}
	}
	if len(msgRefs) > 0 {
		valuesSort := c.ArraySort(c.StringSort(), ts.celValueSort)
		presenceSort := c.ArraySort(c.StringSort(), c.BoolSort())
		mk := ts.InternFuncDecl(funcMkMsgRef, []*smt.Sort{c.StringSort(), valuesSort, presenceSort}, ts.messageRefSort)
		for _, ref := range msgRefs {
			if isAppNamed(ref, funcMkMsgRef) {
				continue
			}
			ax := c.MkEq(c.MkApp(mk, ts.GetMsgTypeName(ref), ts.GetMsgValues(ref), ts.GetMsgPresence(ref)), ref)
			if ref.IsAppOf(ts.messageCons.Accessors[0]) {
				ax = c.MkImplies(ts.IsMessage(ref.Args[0]), ax)
			}
			axioms = append(axioms, ax)
		}
	}
	return axioms
}

func isAppNamed(t *smt.Term, name string) bool {
	return t.IsApp() && t.DeclName() == name
}
