// Package kube teaches the verifier the CEL libraries of Kubernetes
// (k8s.io/apiserver/pkg/cel/library): quantities, the lists extensions, IP
// addresses and CIDRs, semantic versions, named formats and the authorizer.
//
// Values of the libraries' opaque types are encoded as objects (see
// verifier.TypeSystem.DefineObject) holding a canonical representation:
//
//	kubernetes.Quantity    {nanos: int}                        the value in units of 10^-9
//	net.IP                 {family: 4|6, addr: int}            the address as an unsigned integer
//	net.CIDR               {family, addr, prefix: int}         the address as written, unmasked
//	kubernetes.Semver      {major, minor, patch: int, pre: string}
//	kubernetes.NamedFormat {name: string}
//
// so that the libraries' equality is the verifier's: e.g. quantity('1') ==
// quantity('1000m'). Calls on constant arguments are evaluated by the
// libraries themselves, so their results match the runtime exactly; the
// operations on the representations (comparisons, arithmetic, containment,
// address classes, ...) are exact for every input. Conversions from
// non-constant strings are uninterpreted, but consistent with each other
// (e.g. isQuantity(s) holds exactly when quantity(s) doesn't fail), and
// counterexamples that depend on them are reported as inconclusive.
//
// Authorizer checks are not modeled: calls on the authorizer are
// uninterpreted functions, so the same check always has the same outcome.
// Format validation is likewise uninterpreted.
//
// Usage:
//
//	env, _ := cel.NewEnv(kube.EnvOptions()...)
//	v, _ := verifier.New(env, kube.VerifierOptions()...)
package kube

import (
	"fmt"
	"math"
	"sync"

	"cel.dev/cel-go/cel"
	"cel.dev/cel-go/common/decls"
	"cel.dev/cel-go/common/types/ref"
	"k8s.io/apiserver/pkg/cel/library"

	"github.com/swist/cel-go-verifier/smt"
	"github.com/swist/cel-go-verifier/verifier"
)

// Type names of the encoded objects.
const (
	quantityType = "kubernetes.Quantity"
	ipType       = "net.IP"
	cidrType     = "net.CIDR"
	semverType   = "kubernetes.Semver"
	formatType   = "kubernetes.NamedFormat"
)

// EnvOptions declares the Kubernetes CEL libraries the axioms cover, at their
// latest versions.
func EnvOptions() []cel.EnvOption {
	return []cel.EnvOption{
		library.Lists(library.ListsVersion(math.MaxUint32)),
		library.Quantity(),
		library.IP(),
		library.CIDR(library.CIDRVersion(math.MaxUint32)),
		library.SemverLib(library.SemverVersion(math.MaxUint32)),
		library.Format(),
		library.Authz(),
		library.AuthzSelectors(),
	}
}

// VerifierOptions installs the axioms and the witness formatters.
func VerifierOptions() []verifier.Option {
	return []verifier.Option{
		verifier.FunctionAxioms(Axioms()...),
		verifier.MessageFormatters(Formatters()),
		verifier.ObjectConstraints(ObjectConstraints()),
	}
}

// ObjectConstraints constrains values of the libraries' types (e.g. variables
// declared as net.IP) to valid representations.
func ObjectConstraints() map[string]verifier.ObjectConstraint {
	ints := func(ts *verifier.TypeSystem, v *smt.Term, names ...string) []*smt.Term {
		var out []*smt.Term
		for _, n := range names {
			out = append(out, ts.IsInt(ts.ObjectField(v, n)))
		}
		return out
	}
	return map[string]verifier.ObjectConstraint{
		quantityType: func(ts *verifier.TypeSystem, v *smt.Term) *smt.Term {
			c := ts.Ctx()
			return c.MkAnd(append(ints(ts, v, "nanos"), ts.HasExactFields(v, "nanos"))...)
		},
		ipType: func(ts *verifier.TypeSystem, v *smt.Term) *smt.Term {
			c := ts.Ctx()
			parts := append(ints(ts, v, "family", "addr"), ts.HasExactFields(v, "family", "addr"),
				wellFormed(c, intField(ts, v, "family"), intField(ts, v, "addr"), nil))
			return c.MkAnd(parts...)
		},
		cidrType: func(ts *verifier.TypeSystem, v *smt.Term) *smt.Term {
			c := ts.Ctx()
			parts := append(ints(ts, v, "family", "addr", "prefix"), ts.HasExactFields(v, "family", "addr", "prefix"),
				wellFormed(c, intField(ts, v, "family"), intField(ts, v, "addr"), intField(ts, v, "prefix")))
			return c.MkAnd(parts...)
		},
		semverType: func(ts *verifier.TypeSystem, v *smt.Term) *smt.Term {
			c := ts.Ctx()
			parts := append(ints(ts, v, "major", "minor", "patch"), ts.IsString(ts.ObjectField(v, "pre")),
				ts.HasExactFields(v, "major", "minor", "patch", "pre"))
			for _, n := range []string{"major", "minor", "patch"} {
				parts = append(parts, c.MkGe(intField(ts, v, n), c.MkInt(0)))
			}
			return c.MkAnd(parts...)
		},
		formatType: func(ts *verifier.TypeSystem, v *smt.Term) *smt.Term {
			c := ts.Ctx()
			name := ts.ObjectField(v, "name")
			var known []*smt.Term
			for _, k := range formatNames() {
				known = append(known, c.MkEq(name, ts.MkString(library.ConstantFormats[k].Name)))
			}
			return c.MkAnd(ts.HasExactFields(v, "name"), c.MkOr(known...))
		},
	}
}

// UnrollLimit bounds the list elements the lists axioms model exactly; longer
// lists make their results approximate. It matches the verifier's default
// comprehension unroll limit.
const UnrollLimit = 5

var libEnv = sync.OnceValues(func() (*cel.Env, error) {
	return cel.NewEnv(append(EnvOptions(),
		cel.Variable("a", cel.DynType), cel.Variable("b", cel.DynType))...)
})

func libFunctions() map[string]*decls.FunctionDecl {
	env, err := libEnv()
	if err != nil {
		panic(fmt.Sprintf("kube: %v", err))
	}
	return env.Functions()
}

// newAxiom starts the axiom of a library function.
func newAxiom(name string) *verifier.FunctionAxiom {
	fn, ok := libFunctions()[name]
	if !ok {
		panic("kube: unknown function " + name)
	}
	return verifier.NewFunctionAxiom(verifier.FunctionDeclFromCEL(fn))
}

// Axioms returns the axioms of the Kubernetes libraries.
func Axioms() []*verifier.FunctionAxiom {
	var out []*verifier.FunctionAxiom
	out = append(out, quantityAxioms()...)
	out = append(out, ipAxioms()...)
	out = append(out, semverAxioms()...)
	out = append(out, formatAxioms()...)
	out = append(out, listsAxioms()...)
	return mergeAxioms(out)
}

// mergeAxioms combines the axioms of the same function (e.g. ip(string) and
// cidr.ip()) into one.
func mergeAxioms(axioms []*verifier.FunctionAxiom) []*verifier.FunctionAxiom {
	byName := map[string]*verifier.FunctionAxiom{}
	var out []*verifier.FunctionAxiom
	for _, a := range axioms {
		prev, ok := byName[a.Decl.Name]
		if !ok {
			byName[a.Decl.Name] = a
			out = append(out, a)
			continue
		}
		for id, t := range a.Translators {
			prev.Overload(id, t)
		}
	}
	return out
}

// Formatters displays the encoded objects in witnesses.
func Formatters() map[string]verifier.MessageFormatter {
	return map[string]verifier.MessageFormatter{
		quantityType: formatQuantity,
		ipType:       formatIP,
		cidrType:     formatCIDR,
		semverType:   formatSemver,
		formatType:   formatFormat,
	}
}

var programs sync.Map // expression -> cel.Program

// eval evaluates a library expression over a and b (e.g. "quantity(a)").
func eval(expr string, args ...ref.Val) ref.Val {
	p, ok := programs.Load(expr)
	if !ok {
		env, err := libEnv()
		if err != nil {
			panic(fmt.Sprintf("kube: %v", err))
		}
		ast, iss := env.Compile(expr)
		if iss.Err() != nil {
			panic(fmt.Sprintf("kube: compiling %s: %v", expr, iss.Err()))
		}
		prg, err := env.Program(ast)
		if err != nil {
			panic(fmt.Sprintf("kube: %v", err))
		}
		p, _ = programs.LoadOrStore(expr, prg)
	}
	act := map[string]any{}
	for i, a := range args {
		act[string(rune('a'+i))] = a
	}
	out, _, err := p.(cel.Program).Eval(act)
	if err != nil {
		return nil
	}
	return out
}

// constants records the Go value of each constant object, by the name of its reference.
var constants sync.Map

// constObject returns the reference of a constant object named key, recording val.
func constObject(c *smt.Context, ts *verifier.TypeSystem, key string, val any) *smt.Term {
	name := "!kube:" + key
	constants.Store(name, val)
	return c.MkConst(name, ts.MessageRefSort())
}

// constantOf returns the Go value of v if v is a constant object.
func constantOf(ts *verifier.TypeSystem, v *smt.Term) (any, bool) {
	if _, ok := ts.MessageRefOf(v); !ok {
		// Calls wrap their results in dispatch and error propagation, which
		// the simplifier resolves for constants.
		v = ts.Ctx().Simplify(v)
	}
	r, ok := ts.MessageRefOf(v)
	if !ok || !r.IsApp() || len(r.Args) != 0 {
		return nil, false
	}
	return constants.Load(r.DeclName())
}

// fn interns an uninterpreted function.
func fn(ts *verifier.TypeSystem, name string, rng *smt.Sort, domain ...*smt.Sort) *smt.FuncDecl {
	return ts.InternFuncDecl("!kube."+name, domain, rng)
}

// fromString translates a conversion from a string: exactly by the library
// for a literal, and otherwise through uninterpreted functions of the string,
// which makes the result approximate. valid is the condition under which the
// conversion succeeds.
type conversion struct {
	// literal converts a constant; ok is false if it fails.
	literal func(c *smt.Context, ts *verifier.TypeSystem, sink func(*smt.Term), s string) (v *smt.Term, ok bool)
	// symbolic converts a non-constant string, returning the value and when it's valid.
	symbolic func(c *smt.Context, ts *verifier.TypeSystem, sink func(*smt.Term), s *smt.Term) (v, valid *smt.Term)
}

func (conv conversion) translate(c *smt.Context, ts *verifier.TypeSystem, sink func(*smt.Term), arg *smt.Term) (v, approx *smt.Term) {
	if s, ok := ts.StringLiteral(arg); ok {
		if v, ok := conv.literal(c, ts, sink, s); ok {
			return v, c.MkFalse()
		}
		return ts.MkError(), c.MkFalse()
	}
	v, valid := conv.symbolic(c, ts, sink, ts.GetString(arg))
	return c.MkITE(valid, v, ts.MkError()), c.MkTrue()
}

// validity translates the matching is* test of a conversion.
func (conv conversion) validity(c *smt.Context, ts *verifier.TypeSystem, sink func(*smt.Term), arg *smt.Term) (v, approx *smt.Term) {
	if s, ok := ts.StringLiteral(arg); ok {
		_, ok := conv.literal(c, ts, sink, s)
		return ts.MkBool(ok), c.MkFalse()
	}
	_, valid := conv.symbolic(c, ts, sink, ts.GetString(arg))
	return ts.WrapBool(valid), c.MkTrue()
}

// unaryOverload adds a one-argument translator with its own approximation.
func unaryOverload(f *verifier.FunctionAxiom, id string, t func(c *smt.Context, ts *verifier.TypeSystem, sink func(*smt.Term), arg *smt.Term) (v, approx *smt.Term)) {
	f.Overload(id, func(c *smt.Context, ts *verifier.TypeSystem, sink func(*smt.Term), args, approx []*smt.Term) (verifier.OverloadResult, bool) {
		v, a := t(c, ts, sink, args[0])
		return verifier.OverloadResult{Value: v, Approx: c.MkOr(approx[0], c.MkAnd(a, c.MkNot(ts.IsUnknown(v))))}, true
	})
}

// binaryOverload adds a two-argument translator with its own approximation.
func binaryOverload(f *verifier.FunctionAxiom, id string, t func(c *smt.Context, ts *verifier.TypeSystem, sink func(*smt.Term), a, b *smt.Term) (v, approx *smt.Term)) {
	f.Overload(id, func(c *smt.Context, ts *verifier.TypeSystem, sink func(*smt.Term), args, approx []*smt.Term) (verifier.OverloadResult, bool) {
		v, a := t(c, ts, sink, args[0], args[1])
		return verifier.OverloadResult{Value: v, Approx: c.MkOr(approx[0], approx[1], a)}, true
	})
}

// intField returns an int field of an object.
func intField(ts *verifier.TypeSystem, v *smt.Term, name string) *smt.Term {
	return ts.GetInt(ts.ObjectField(v, name))
}

// sign returns -1, 0 or 1 by the sign of x - y.
func cmpInts(c *smt.Context, ts *verifier.TypeSystem, x, y *smt.Term) *smt.Term {
	return ts.WrapInt(c.MkITE(c.MkLt(x, y), c.MkInt(-1), c.MkITE(c.MkGt(x, y), c.MkInt(1), c.MkInt(0))))
}
