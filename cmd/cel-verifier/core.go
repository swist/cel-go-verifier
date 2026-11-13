package main

import (
	"time"

	"cel.dev/cel-go/cel"
	"cel.dev/cel-go/ext"

	"github.com/swist/cel-go-verifier/policyverifier"
	"github.com/swist/cel-go-verifier/smt"
	"github.com/swist/cel-go-verifier/verifier"
)

// options configures a verification run.
type options struct {
	timeout     time.Duration
	unrollLimit int
	unknowns    []string
	backend     smt.Backend
}

// recorderHook, if set, records every solver interaction (for tests).
var recorderHook func() smt.Recorder

func defaultOptions() options { return options{timeout: 10 * time.Second, unrollLimit: 5} }

// compileError reports an expression that doesn't compile.
type compileError struct{ msg string }

func (e *compileError) Error() string { return e.msg }

// newEnv returns the environment of the tool: the standard library, the
// extension libraries cel-java's verifier tool declares, and the variables.
func newEnv(vars []variable) (*cel.Env, error) {
	opts := []cel.EnvOption{
		ext.Bindings(),
		ext.TwoVarComprehensions(),
		ext.Encoders(),
		ext.Lists(),
		ext.Math(),
		cel.OptionalTypes(),
		ext.Protos(),
		ext.Regex(),
		ext.Sets(),
		ext.Strings(),
	}
	for _, v := range vars {
		opts = append(opts, cel.Variable(v.name, v.typ))
	}
	return cel.NewEnv(opts...)
}

func newVerifier(env *cel.Env, o options) (*verifier.Verifier, error) {
	vopts := []verifier.Option{
		verifier.Timeout(o.timeout),
		verifier.ComprehensionUnrollLimit(o.unrollLimit),
		verifier.UnknownIdentifiers(o.unknowns...),
	}
	if recorderHook != nil {
		vopts = append(vopts, verifier.Recorder(recorderHook))
	}
	if o.backend != nil {
		vopts = append(vopts, verifier.Backend(o.backend))
	}
	return verifier.New(env, vopts...)
}

func compile(env *cel.Env, expr string) (*cel.Ast, error) {
	a, iss := env.Compile(expr)
	if iss.Err() != nil {
		return nil, &compileError{iss.Err().Error()}
	}
	return a, nil
}

func setup(vars []variable, o options, exprs ...string) (*verifier.Verifier, []*cel.Ast, error) {
	env, err := newEnv(vars)
	if err != nil {
		return nil, nil, err
	}
	var asts []*cel.Ast
	for _, e := range exprs {
		a, err := compile(env, e)
		if err != nil {
			return nil, nil, err
		}
		asts = append(asts, a)
	}
	v, err := newVerifier(env, o)
	return v, asts, err
}

// checkSatisfiable checks whether an expression can evaluate to true.
func checkSatisfiable(expr string, vars []variable, o options) (verifier.Result, error) {
	v, asts, err := setup(vars, o, expr)
	if err != nil {
		return verifier.Result{}, err
	}
	return v.IsSatisfiable(asts[0])
}

// checkValid checks whether an expression is always true.
func checkValid(expr string, vars []variable, o options) (verifier.Result, error) {
	v, asts, err := setup(vars, o, expr)
	if err != nil {
		return verifier.Result{}, err
	}
	return v.IsAlwaysTrue(asts[0])
}

// verifyEquivalence checks whether two expressions always evaluate to the same result.
func verifyEquivalence(exprA, exprB string, vars []variable, o options) (verifier.Result, error) {
	v, asts, err := setup(vars, o, exprA, exprB)
	if err != nil {
		return verifier.Result{}, err
	}
	return v.VerifyEquivalence(asts[0], asts[1])
}

func newPolicyVerifier(vars []variable, o options) (*policyverifier.Verifier, error) {
	env, err := newEnv(vars)
	if err != nil {
		return nil, err
	}
	v, err := newVerifier(env, o)
	if err != nil {
		return nil, err
	}
	return policyverifier.New(env, v), nil
}

// verifyPolicyInvariants checks the invariants of a YAML policy's verification section.
func verifyPolicyInvariants(yamlSrc string, vars []variable, o options) ([]namedResult, error) {
	p, err := policyverifier.Parse(yamlSrc, "<policy>")
	if err != nil {
		return nil, err
	}
	pv, err := newPolicyVerifier(vars, o)
	if err != nil {
		return nil, err
	}
	results, err := pv.VerifyInvariants(p)
	if err != nil {
		return nil, err
	}
	out := make([]namedResult, len(results))
	for i, r := range results {
		out[i] = namedResult{r.ID, r.Result}
	}
	return out, nil
}

// verifyPolicyEquivalence checks whether two YAML policies always produce the same result.
func verifyPolicyEquivalence(yamlA, yamlB string, vars []variable, o options) (verifier.Result, error) {
	a, err := policyverifier.Parse(yamlA, "<policy a>")
	if err != nil {
		return verifier.Result{}, err
	}
	b, err := policyverifier.Parse(yamlB, "<policy b>")
	if err != nil {
		return verifier.Result{}, err
	}
	pv, err := newPolicyVerifier(vars, o)
	if err != nil {
		return verifier.Result{}, err
	}
	return pv.VerifyEquivalence(a, b)
}
