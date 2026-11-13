package kube

import (
	"fmt"
	"sort"

	"cel.dev/cel-go/common/types"
	"cel.dev/cel-go/common/types/ref"
	"k8s.io/apiserver/pkg/cel/library"

	"github.com/swist/cel-go-verifier/smt"
	"github.com/swist/cel-go-verifier/verifier"
)

// Named formats are encoded by their name, which their equality compares.
// format.<name>() and format.named(name) are exact; validation is
// uninterpreted.

func formatNames() []string {
	var names []string
	for k := range library.ConstantFormats {
		names = append(names, k)
	}
	sort.Strings(names)
	return names
}

func constFormat(c *smt.Context, ts *verifier.TypeSystem, sink func(*smt.Term), key string) *smt.Term {
	f := library.ConstantFormats[key]
	r := constObject(c, ts, "format:"+f.Name, f)
	return ts.DefineObject(sink, r, formatType, verifier.ObjectField{Name: "name", Value: ts.MkString(f.Name)})
}

func formatAxioms() []*verifier.FunctionAxiom {
	var out []*verifier.FunctionAxiom
	for _, key := range formatNames() {
		key := key
		name := "format." + key
		out = append(out, newAxiom(name).Overload(name, func(c *smt.Context, ts *verifier.TypeSystem, sink func(*smt.Term), _, _ []*smt.Term) (verifier.OverloadResult, bool) {
			return verifier.OverloadResult{Value: constFormat(c, ts, sink, key), Approx: c.MkFalse()}, true
		}))
	}
	named := newAxiom("format.named").Unary("format-named", func(c *smt.Context, ts *verifier.TypeSystem, sink func(*smt.Term), name *smt.Term) (*smt.Term, bool) {
		some := func(f *smt.Term) *smt.Term {
			r := c.MkApp(ts.OptionalOfRefFunc(), f)
			sink(c.MkEq(ts.GetOptionalValue(r), f))
			sink(ts.OptHasValue(r))
			return ts.MkOptionalOf(r)
		}
		if s, ok := ts.StringLiteral(name); ok {
			if _, ok := library.ConstantFormats[s]; ok {
				return some(constFormat(c, ts, sink, s)), true
			}
			return ts.MkOptionalNone(), true
		}
		out := ts.MkOptionalNone()
		str := ts.GetString(name)
		for _, key := range formatNames() {
			out = c.MkITE(c.MkEq(str, verifier.MkZ3String(c, key)), some(constFormat(c, ts, sink, key)), out)
		}
		return out, true
	}, false)
	return append(out, named)
}

func formatFormat(fields map[string]verifier.MessageField) (ref.Val, string, bool) {
	name, ok := fields["name"].Value.(types.String)
	if !ok {
		return nil, "", false
	}
	for _, key := range formatNames() {
		if f := library.ConstantFormats[key]; f.Name == string(name) {
			return f, fmt.Sprintf("format.%s()", key), true
		}
	}
	return nil, "", false
}
