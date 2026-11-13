// Package policyverifier verifies CEL policies (cel.dev/cel-go/policy): the
// equivalence of two policies, and invariants declared in a policy's
// verification section. It is a port of cel-java's CelPolicyVerifier.
//
// A verification section lists invariants that must hold for every input, and
// variables they may use:
//
//	verification:
//	  variables:
//	    - is_denied: rule.result == 'DENY'
//	  invariants:
//	    - id: no_unapproved_privileged_prod
//	      assume:
//	        - variables.is_privileged_container
//	        - "!variables.has_security_approval"
//	      assert: rule.result == 'DENY'
//
// Invariants may reference the policy's variables, the verification
// variables, and the policy's result as rule.result.
package policyverifier

import (
	"fmt"
	"strings"

	"cel.dev/cel-go/cel"
	"cel.dev/cel-go/common"
	"cel.dev/cel-go/policy"
	"go.yaml.in/yaml/v3"

	"github.com/swist/cel-go-verifier/verifier"
)

const resultIdentifier = "rule.result"

const verificationMetadata = "verification"

// Verification is the verification section of a policy.
type Verification struct {
	Variables  []Variable
	Invariants []Invariant
}

// Variable is a verification variable.
type Variable struct {
	Name, Expression string
}

// Invariant is a property that must hold for every input.
type Invariant struct {
	ID, Description string
	// Assume and Assert are conjunctions of CEL expressions.
	Assume, Assert []string
}

func conjunction(clauses []string) string {
	switch len(clauses) {
	case 0:
		return "true"
	case 1:
		return clauses[0]
	}
	parts := make([]string, len(clauses))
	for i, c := range clauses {
		parts[i] = "(" + c + ")"
	}
	return strings.Join(parts, " && ")
}

// AssumeSource is the assumption as one expression.
func (i Invariant) AssumeSource() string { return conjunction(i.Assume) }

// AssertSource is the assertion as one expression.
func (i Invariant) AssertSource() string { return conjunction(i.Assert) }

// VerificationOf returns the verification section parsed with TagVisitor, if any.
func VerificationOf(p *policy.Policy) *Verification {
	v, ok := p.Metadata(verificationMetadata)
	if !ok {
		return nil
	}
	return v.(*Verification)
}

// TagVisitor parses the verification section into the policy's metadata, and
// delegates other tags to base (e.g. policy.DefaultTagVisitor()).
func TagVisitor(base policy.TagVisitor) policy.TagVisitor { return &tagVisitor{base} }

type tagVisitor struct{ policy.TagVisitor }

func (v *tagVisitor) PolicyTag(ctx policy.ParserContext, id int64, tag string, node *yaml.Node, p *policy.Policy) {
	if tag != verificationMetadata {
		v.TagVisitor.PolicyTag(ctx, id, tag, node, p)
		return
	}
	ver, err := parseVerification(node)
	if err != nil {
		ctx.ReportErrorAtID(id, "invalid verification section: %v", err)
		return
	}
	p.SetMetadata(verificationMetadata, ver)
}

type yamlVerification struct {
	Variables  []map[string]string `yaml:"variables"`
	Invariants []struct {
		ID          string      `yaml:"id"`
		Description string      `yaml:"description"`
		Assume      stringOrSeq `yaml:"assume"`
		Assert      stringOrSeq `yaml:"assert"`
	} `yaml:"invariants"`
}

type stringOrSeq []string

func (s *stringOrSeq) UnmarshalYAML(n *yaml.Node) error {
	if n.Kind == yaml.ScalarNode {
		*s = []string{n.Value}
		return nil
	}
	var out []string
	if err := n.Decode(&out); err != nil {
		return err
	}
	*s = out
	return nil
}

func parseVerification(node *yaml.Node) (*Verification, error) {
	var y yamlVerification
	if err := node.Decode(&y); err != nil {
		return nil, err
	}
	ver := &Verification{}
	for _, m := range y.Variables {
		if name, ok := m["name"]; ok {
			ver.Variables = append(ver.Variables, Variable{name, m["expression"]})
			continue
		}
		if len(m) != 1 {
			return nil, fmt.Errorf("a verification variable needs a name and an expression")
		}
		for k, e := range m {
			ver.Variables = append(ver.Variables, Variable{k, e})
		}
	}
	for _, inv := range y.Invariants {
		ver.Invariants = append(ver.Invariants, Invariant{inv.ID, inv.Description, inv.Assume, inv.Assert})
	}
	return ver, nil
}

// Parse parses a YAML policy with simple variables (- name: expression) and a
// verification section. Extra options (e.g. another tag visitor wrapped with
// TagVisitor) apply after the defaults.
func Parse(src, location string, opts ...policy.ParserOption) (*policy.Policy, error) {
	opts = append([]policy.ParserOption{policy.SimpleVariables(), policy.CustomTagVisitor(TagVisitor(policy.DefaultTagVisitor()))}, opts...)
	parser, err := policy.NewParser(opts...)
	if err != nil {
		return nil, err
	}
	p, iss := parser.Parse(policy.StringSource(src, location))
	if iss.Err() != nil {
		return nil, &PolicyError{iss.Err().Error()}
	}
	return p, nil
}

// Verifier verifies policies compiled in an environment.
type Verifier struct {
	env      *cel.Env
	v        *verifier.Verifier
	compiler []policy.CompilerOption
	optimize func(*cel.Env, *cel.Ast) (*cel.Ast, error)
}

// Option configures a Verifier.
type Option func(*Verifier)

// CompilerOptions sets the options of the policy compiler.
func CompilerOptions(opts ...policy.CompilerOption) Option {
	return func(pv *Verifier) { pv.compiler = append(pv.compiler, opts...) }
}

// Optimize post-processes compiled policies, e.g. with a common subexpression eliminator.
func Optimize(f func(*cel.Env, *cel.Ast) (*cel.Ast, error)) Option {
	return func(pv *Verifier) { pv.optimize = f }
}

// New returns a policy verifier that compiles policies in env and checks them with v.
func New(env *cel.Env, v *verifier.Verifier, opts ...Option) *Verifier {
	pv := &Verifier{env: env, v: v}
	for _, o := range opts {
		o(pv)
	}
	return pv
}

// Compile compiles and composes a policy into one expression.
func (pv *Verifier) Compile(p *policy.Policy) (*cel.Ast, error) {
	a, iss := policy.Compile(pv.env, p, pv.compiler...)
	if iss.Err() != nil {
		return nil, &PolicyError{iss.Err().Error()}
	}
	if pv.optimize != nil {
		return pv.optimize(pv.env, a)
	}
	return a, nil
}

// VerifyEquivalence checks whether two policies produce the same result for every input.
func (pv *Verifier) VerifyEquivalence(a, b *policy.Policy) (verifier.Result, error) {
	astA, err := pv.Compile(a)
	if err != nil {
		return verifier.Result{}, err
	}
	astB, err := pv.Compile(b)
	if err != nil {
		return verifier.Result{}, err
	}
	return pv.v.VerifyEquivalence(astA, astB)
}

// InvariantResult is the outcome of verifying one invariant.
type InvariantResult struct {
	ID     string
	Result verifier.Result
}

// VerifyInvariants checks the invariants of the policy's verification section, in order.
func (pv *Verifier) VerifyInvariants(p *policy.Policy) ([]InvariantResult, error) {
	ver := VerificationOf(p)
	if ver == nil || len(ver.Invariants) == 0 {
		return nil, nil
	}
	return pv.VerifyInvariantsOf(p, ver)
}

// VerifyInvariantsOf checks invariants given separately from the policy.
func (pv *Verifier) VerifyInvariantsOf(p *policy.Policy, ver *Verification) ([]InvariantResult, error) {
	rule, iss := policy.CompileRule(pv.env, p, pv.compiler...)
	if iss.Err() != nil {
		return nil, &PolicyError{iss.Err().Error()}
	}
	composer, err := policy.NewRuleComposer(pv.env)
	if err != nil {
		return nil, err
	}
	composed, iss := composer.Compose(rule)
	if iss.Err() != nil {
		return nil, &PolicyError{iss.Err().Error()}
	}
	var bound []verifier.BoundSymbol
	var decls []cel.EnvOption
	for _, v := range rule.Variables() {
		d := v.Declaration()
		decls = append(decls, cel.Variable(d.Name(), d.Type()))
		bound = append(bound, verifier.BoundSymbol{Name: d.Name(), AST: v.Expr()})
	}
	bound = append(bound, verifier.BoundSymbol{Name: resultIdentifier, AST: composed})
	decls = append(decls, cel.Variable(resultIdentifier, composed.OutputType()))
	env, err := pv.env.Extend(decls...)
	if err != nil {
		return nil, err
	}
	for _, v := range ver.Variables {
		a, err := compileIn(env, v.Expression, "verification.variables."+v.Name)
		if err != nil {
			return nil, err
		}
		name := "variables." + v.Name
		bound = append(bound, verifier.BoundSymbol{Name: name, AST: a})
		if env, err = env.Extend(cel.Variable(name, a.OutputType())); err != nil {
			return nil, err
		}
	}
	var out []InvariantResult
	for _, inv := range ver.Invariants {
		assume, err := compileIn(env, inv.AssumeSource(), "invariant."+inv.ID+".assume")
		if err != nil {
			return nil, err
		}
		assertion, err := compileIn(env, inv.AssertSource(), "invariant."+inv.ID+".assert")
		if err != nil {
			return nil, err
		}
		r, err := pv.v.VerifyImplication(assume, assertion, bound, fmt.Sprintf("Invariant '%s'", inv.ID))
		if err != nil {
			return nil, err
		}
		out = append(out, InvariantResult{inv.ID, r})
	}
	return out, nil
}

// PolicyError reports a policy that doesn't parse, compile or compose.
type PolicyError struct{ msg string }

func (e *PolicyError) Error() string { return e.msg }

// ValidationError reports an invalid expression in a verification section.
type ValidationError struct{ msg string }

func (e *ValidationError) Error() string { return e.msg }

func compileIn(env *cel.Env, src, description string) (*cel.Ast, error) {
	a, iss := env.CompileSource(common.NewStringSource(src, description))
	if iss.Err() != nil {
		return nil, &ValidationError{iss.Err().Error()}
	}
	return a, nil
}
