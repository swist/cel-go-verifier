// Package verifier proves properties of CEL expressions with the Z3 SMT
// solver: satisfiability, validity, equivalence and implication. It is a Go
// port of cel-java's verifier (dev.cel.verifier) and produces the same Z3
// queries for the same checked expressions.
package verifier

import (
	"errors"
	"fmt"
	"strings"
	"time"

	"cel.dev/cel-go/cel"
	"cel.dev/cel-go/common/ast"

	"github.com/swist/cel-go-verifier/smt"
	"github.com/swist/cel-go-verifier/smt/z3proc"
)

// Status is the outcome of a verification.
type Status int

// Statuses.
const (
	// Verified means the property was proven for all inputs.
	Verified Status = iota
	// Violated means the property was disproven with a concrete counterexample.
	Violated
	// Inconclusive means the outcome depends on what the verifier doesn't model exactly.
	Inconclusive
)

func (s Status) String() string {
	switch s {
	case Verified:
		return "VERIFIED"
	case Violated:
		return "VIOLATED"
	}
	return "INCONCLUSIVE"
}

// Result is the outcome of a verification check.
type Result struct {
	Status Status
	// Reason is the primary reason for the outcome.
	Reason string
	// Counterexample describes the witness, if any.
	Counterexample string
	// Witness is the counterexample or satisfying input found, if any.
	Witness *Witness
}

// Message details the outcome, including the witness.
func (r Result) Message() string { return r.Reason + r.Counterexample }

func verifiedResult() Result                  { return Result{Status: Verified} }
func failedResult(reason string) Result       { return Result{Status: Violated, Reason: reason} }
func inconclusiveResult(reason string) Result { return Result{Status: Inconclusive, Reason: reason} }

func resultWithWitness(st Status, reason string, w *Witness, isCounterexample bool) Result {
	return Result{Status: st, Reason: reason, Counterexample: describeWitness(w, st == Inconclusive, isCounterexample), Witness: w}
}

func describeWitness(w *Witness, approximate, isCounterexample bool) string {
	if len(w.Names) == 0 {
		if isCounterexample {
			return " (The expression fails unconditionally, regardless of input state)"
		}
		return " (The expression is satisfiable unconditionally, regardless of input state)"
	}
	var sb strings.Builder
	switch {
	case isCounterexample && approximate:
		sb.WriteString(" Potential counterexample input:")
	case isCounterexample:
		sb.WriteString(" Counterexample input:")
	case approximate:
		sb.WriteString(" Potential satisfying input:")
	default:
		sb.WriteString(" Satisfying input:")
	}
	for _, n := range w.Names {
		sb.WriteString("\n  " + n + " = " + w.Variables[n].Display)
	}
	return sb.String()
}

// Error is returned when verification fails or times out.
type Error struct{ msg string }

func (e *Error) Error() string { return e.msg }

// Verifier proves properties of checked CEL ASTs. It is safe for concurrent use.
type Verifier struct {
	env            *cel.Env
	timeout        time.Duration
	limit          int
	unknownIdents  map[string]bool
	registry       *functionRegistry
	typeProvider   TypeProvider
	backend        smt.Backend
	recorder       func() smt.Recorder
	canonicalize   bool
	extra          []*FunctionAxiom
	formatters     map[string]MessageFormatter
	objConstraints map[string]ObjectConstraint
}

// Option configures a Verifier.
type Option func(*Verifier) error

// Timeout sets the solver timeout (default 10s).
func Timeout(d time.Duration) Option {
	return func(v *Verifier) error {
		if d <= 0 {
			return errors.New("verifier: timeout must be strictly positive")
		}
		v.timeout = d
		return nil
	}
}

// ComprehensionUnrollLimit sets how many iterations of comprehensions over
// non-literal ranges are modelled (default 5).
func ComprehensionUnrollLimit(n int) Option {
	return func(v *Verifier) error {
		if n < 0 {
			return errors.New("verifier: unrollLimit must be non-negative")
		}
		v.limit = n
		return nil
	}
}

// UnknownIdentifiers declares variables that may be unknown, as in partial evaluation.
func UnknownIdentifiers(names ...string) Option {
	return func(v *Verifier) error {
		for _, n := range names {
			v.unknownIdents[n] = true
		}
		return nil
	}
}

// Types sets the provider of the message types the verifier models.
func Types(tp TypeProvider) Option {
	return func(v *Verifier) error { v.typeProvider = tp; return nil }
}

// FunctionAxioms adds axioms for functions beyond the standard library.
func FunctionAxioms(axioms ...*FunctionAxiom) Option {
	return func(v *Verifier) error {
		v.extra = append(v.extra, axioms...)
		return nil
	}
}

// Backend sets the solver backend (default: the z3 executable, see package z3proc).
func Backend(b smt.Backend) Option {
	return func(v *Verifier) error { v.backend = b; return nil }
}

// Recorder installs a factory of recorders that observe every solver interaction.
func Recorder(f func() smt.Recorder) Option {
	return func(v *Verifier) error { v.recorder = f; return nil }
}

// New returns a verifier for ASTs checked in env.
func New(env *cel.Env, opts ...Option) (*Verifier, error) {
	v := &Verifier{
		env: env, timeout: 10 * time.Second, limit: 5, unknownIdents: map[string]bool{},
		typeProvider: emptyTypeProvider{}, canonicalize: true,
	}
	for _, o := range opts {
		if err := o(v); err != nil {
			return nil, err
		}
	}
	r, err := newFunctionRegistry(append(StandardAxioms(), v.extra...))
	if err != nil {
		return nil, err
	}
	v.registry = r
	if v.backend == nil {
		v.backend = z3proc.New()
	}
	return v, nil
}

type emptyTypeProvider struct{}

func (emptyTypeProvider) StructTypeNames() []string                  { return nil }
func (emptyTypeProvider) FieldType(string, string) (FieldInfo, bool) { return FieldInfo{}, false }

// query is the state of one verification query.
type query struct {
	v      *Verifier
	c      *smt.Context
	tr     *astTranslator
	method string
}

func (v *Verifier) newQuery(method string, parameterizeUnknowns bool) *query {
	c := smt.NewContext(v.backend)
	tr := newASTTranslator(c, v.limit, v.unknownIdents, v.registry, v.typeProvider, parameterizeUnknowns)
	tr.ts.formatters = v.formatters
	tr.ts.objectConstraints = v.objConstraints
	return &query{v: v, c: c, tr: tr, method: method}
}

func (q *query) close() { q.v.backend.Close(q.c) }

func checked(a *cel.Ast, what string) (*ast.AST, error) {
	if a == nil || !a.IsChecked() {
		return nil, fmt.Errorf("verifier: %s must be type-checked", what)
	}
	return a.NativeRep(), nil
}

// translate runs f, converting translation panics to errors.
func translate[T any](f func() T) (out T, err error) {
	defer func() {
		if r := recover(); r != nil {
			if e, ok := r.(error); ok {
				err = fmt.Errorf("verifier: translation failed: %w", e)
			} else {
				err = fmt.Errorf("verifier: translation failed: %v", r)
			}
		}
	}()
	return f(), nil
}

// IsSatisfiable checks whether a can evaluate to true. A Verified result carries a satisfying input.
func (v *Verifier) IsSatisfiable(a *cel.Ast) (Result, error) {
	n, err := checked(a, "AST")
	if err != nil {
		return Result{}, err
	}
	return v.checkSatisfiability("isSatisfiable", n, false)
}

// IsAlwaysTrue checks whether a evaluates to true for every input.
func (v *Verifier) IsAlwaysTrue(a *cel.Ast) (Result, error) {
	n, err := checked(a, "AST")
	if err != nil {
		return Result{}, err
	}
	return v.checkSatisfiability("isAlwaysTrue", n, true)
}

func (v *Verifier) checkSatisfiability(method string, a *ast.AST, counterexample bool) (Result, error) {
	q := v.newQuery(method, false)
	defer q.close()
	type prep struct{ cond, taint, unknown *smt.Term }
	p, err := translate(func() prep {
		c := q.c
		res := q.tr.translate(a)
		isTrue := q.tr.isTrue(res.z3)
		if counterexample {
			return prep{c.MkNot(isTrue), res.approx, c.MkFalse()}
		}
		return prep{isTrue, res.approx, c.MkAnd(q.tr.ts.IsUnknown(res.z3), res.approx)}
	})
	if err != nil {
		return Result{}, err
	}
	if counterexample {
		return q.search(p.cond, p.taint, p.unknown, true, "a counterexample", "Condition is not always true.")
	}
	return q.search(p.cond, p.taint, p.unknown, false, "a satisfying input", "Condition is satisfiable.")
}

// VerifyEquivalence checks whether a and b evaluate to the same result for every input.
func (v *Verifier) VerifyEquivalence(a, b *cel.Ast) (Result, error) {
	if _, err := checked(a, "astA"); err != nil {
		return Result{}, err
	}
	if _, err := checked(b, "astB"); err != nil {
		return Result{}, err
	}
	if v.canonicalize {
		if ca, cb, err := v.canonicalizePair(a, b); err == nil {
			a, b = ca, cb
		}
	}
	q := v.newQuery("verifyEquivalence", true)
	defer q.close()
	type prep struct{ cond, taint *smt.Term }
	p, err := translate(func() prep {
		c := q.c
		ta := q.tr.translate(a.NativeRep())
		tb := q.tr.translate(b.NativeRep())
		divergence := c.MkNot(c.MkEq(ta.z3, tb.z3))
		// Parameterized unknowns are keyed on the operation producing them, so two distinct
		// unknowns may still be equivalent.
		taint := MkOrFlattened(c, ta.approx, tb.approx,
			q.tr.x.recordApproximation("unknown results, which are compared only by their origin",
				c.MkAnd(q.tr.ts.IsUnknown(ta.z3), q.tr.ts.IsUnknown(tb.z3))))
		return prep{divergence, taint}
	})
	if err != nil {
		return Result{}, err
	}
	return q.search(p.cond, p.taint, q.c.MkFalse(), true, "a divergence", "Equivalence violation detected.")
}

// VerifyImplication checks that assert holds whenever assume does. Bound symbols
// (e.g. rule.result) are translated first and visible to both.
func (v *Verifier) VerifyImplication(assume, assertion *cel.Ast, bound []BoundSymbol, subject string) (Result, error) {
	am, err := checked(assume, "assumeAst")
	if err != nil {
		return Result{}, err
	}
	as, err := checked(assertion, "assertAst")
	if err != nil {
		return Result{}, err
	}
	for _, b := range bound {
		if _, err := checked(b.AST, fmt.Sprintf("boundSymbol AST for '%s'", b.Name)); err != nil {
			return Result{}, err
		}
	}
	q := v.newQuery("verifyImplication", false)
	defer q.close()
	type prep struct{ cond, taint, unknown *smt.Term }
	p, err := translate(func() prep {
		c, ts := q.c, q.tr.ts
		for _, b := range bound {
			q.tr.bindSymbol(b.Name, q.tr.translate(b.AST.NativeRep()))
		}
		at := q.tr.translate(am)
		st := q.tr.translate(as)
		assumeCond := q.tr.isTrue(at.z3)
		assertCond := q.tr.isTrue(st.z3)
		violation := c.MkAnd(assumeCond, c.MkNot(assertCond))
		taint := MkOrFlattened(c, at.approx, st.approx)
		unknown := c.MkAnd(ts.IsUnknown(at.z3), at.approx, c.MkNot(c.MkAnd(assertCond, c.MkNot(st.approx))))
		return prep{violation, taint, unknown}
	})
	if err != nil {
		return Result{}, err
	}
	return q.search(p.cond, p.taint, p.unknown, true, "a counterexample", subject+" violation detected.")
}

// BoundSymbol binds a name to the value of an AST during VerifyImplication.
type BoundSymbol struct {
	Name string
	AST  *cel.Ast
}

// search looks for a match of cond: first an exact one, then an approximate
// one, then an unmodelled result satisfying unknownCond that may stand in for one.
func (q *query) search(cond, taint, unknownCond *smt.Term, isCounterexample bool, candidate, exactMessage string) (Result, error) {
	c := q.c
	s, err := q.v.backend.NewSolver(c, q.v.timeout)
	if err != nil {
		return Result{}, err
	}
	defer s.Close()
	if q.v.recorder != nil {
		rec := q.v.recorder()
		rec.NewSolver()
		if mr, ok := rec.(interface{ Method(string) }); ok {
			mr.Method(q.method)
		}
		s = &smt.RecordingSolver{Solver: s, Rec: rec}
	}
	s.Assert(q.tr.x.constraints...)

	// Pass 1: an exact match.
	st, err := q.checkSat(s, cond, c.MkNot(taint))
	if err != nil {
		return Result{}, err
	}
	switch st {
	case smt.Sat:
		w, err := q.witness(s.Model())
		if err != nil {
			return Result{}, err
		}
		if isCounterexample {
			return resultWithWitness(Violated, exactMessage, w, true), nil
		}
		return resultWithWitness(Verified, exactMessage, w, false), nil
	case smt.Unknown:
		return solverGaveUp(s), nil
	}

	// Pass 2: an approximate match.
	st, err = q.checkSat(s, cond)
	if err != nil {
		return Result{}, err
	}
	switch st {
	case smt.Sat:
		m := s.Model()
		reason, err := q.inconclusiveReason(candidate, m, taint)
		if err != nil {
			return Result{}, err
		}
		w, err := q.witness(m)
		if err != nil {
			return Result{}, err
		}
		return resultWithWitness(Inconclusive, reason, w, isCounterexample), nil
	case smt.Unknown:
		return solverGaveUp(s), nil
	}

	// Pass 3: an unmodelled result.
	st, err = q.checkSat(s, unknownCond, q.tr.x.hasUnmodeledResult())
	if err != nil {
		return Result{}, err
	}
	switch st {
	case smt.Sat:
		reason, err := q.inconclusiveReason(candidate, s.Model(), taint)
		if err != nil {
			return Result{}, err
		}
		return inconclusiveResult(reason), nil
	case smt.Unknown:
		return solverGaveUp(s), nil
	}
	if isCounterexample {
		return verifiedResult(), nil
	}
	return failedResult("Condition is not satisfiable."), nil
}

// checkSat checks the assertions on top of the solver's, refining the
// definitions of doubles the model gets wrong. The assertions are left in
// place unless they're unsatisfiable.
func (q *query) checkSat(s smt.Solver, assertions ...*smt.Term) (smt.Status, error) {
	ts := q.tr.ts
	s.Push()
	s.Assert(assertions...)
	st, err := s.Check()
	if err != nil {
		return st, err
	}
	for st == smt.Sat {
		defs, err := ts.defineDoublesContradictedBy(s.Model())
		if err != nil {
			return st, err
		}
		if len(defs) == 0 {
			break
		}
		s.Pop()
		s.Assert(defs...)
		s.Push()
		s.Assert(assertions...)
		if st, err = s.Check(); err != nil {
			return st, err
		}
	}
	switch st {
	case smt.Unsat:
		s.Pop()
	case smt.Unknown:
		if r := s.ReasonUnknown(); r == "timeout" || r == "canceled" {
			return st, &Error{"Verification timed out: " + r}
		}
	}
	return st, nil
}

func solverGaveUp(s smt.Solver) Result {
	return inconclusiveResult("Inconclusive: the solver returned unknown status (" + s.ReasonUnknown() + ").")
}

func (q *query) inconclusiveReason(candidate string, m smt.Model, taint *smt.Term) (string, error) {
	sources, err := q.tr.x.approximationSources(m, taint)
	if err != nil {
		return "", err
	}
	s := "Inconclusive: " + candidate + " may exist, but it depends on what the verifier doesn't model exactly"
	if len(sources) == 0 {
		return s + ".", nil
	}
	return s + ": " + strings.Join(sources, ", ") + ".", nil
}

func (q *query) witness(m smt.Model) (*Witness, error) {
	return generateWitness(q.tr.ts, m, q.v.limit, q.tr.x.inputVars)
}

// DisableCanonicalization skips the canonicalization of ASTs before equivalence checks.
func DisableCanonicalization() Option {
	return func(v *Verifier) error { v.canonicalize = false; return nil }
}
