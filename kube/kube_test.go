package kube_test

import (
	"strconv"
	"strings"
	"testing"

	"cel.dev/cel-go/cel"
	"cel.dev/cel-go/common/types"
	apiservercel "k8s.io/apiserver/pkg/cel"
	"k8s.io/apiserver/pkg/cel/library"

	"github.com/swist/cel-go-verifier/kube"
	"github.com/swist/cel-go-verifier/smt/z3proc"
	"github.com/swist/cel-go-verifier/verifier"
)

func requireZ3(t *testing.T) {
	t.Helper()
	if !z3proc.New().Available() {
		t.Skip("z3 not found; set Z3_PATH")
	}
}

func newEnv(t *testing.T, vars ...cel.EnvOption) *cel.Env {
	t.Helper()
	env, err := cel.NewEnv(append(append(kube.EnvOptions(), cel.OptionalTypes()), vars...)...)
	if err != nil {
		t.Fatal(err)
	}
	return env
}

func newVerifier(t *testing.T, env *cel.Env) *verifier.Verifier {
	t.Helper()
	v, err := verifier.New(env, kube.VerifierOptions()...)
	if err != nil {
		t.Fatal(err)
	}
	return v
}

func compile(t *testing.T, env *cel.Env, expr string) *cel.Ast {
	t.Helper()
	a, iss := env.Compile(expr)
	if iss.Err() != nil {
		t.Fatalf("compile %q: %v", expr, iss.Err())
	}
	return a
}

// TestConstantsMatchRuntime checks closed expressions: each must be proven to
// be what the Kubernetes runtime evaluates it to. The operations on the
// representations (comparisons, arithmetic, containment, ...) are translated
// symbolically, so this checks them against the libraries.
func TestConstantsMatchRuntime(t *testing.T) {
	requireZ3(t)
	exprs := []string{
		// Quantities.
		"quantity('1') == quantity('1000m')",
		"quantity('1Gi') == quantity('1G')",
		"quantity('1Gi').isGreaterThan(quantity('1G'))",
		"quantity('500m').isLessThan(quantity('1'))",
		"quantity('1Ki').compareTo(quantity('1024'))",
		"quantity('2').compareTo(quantity('3'))",
		"sign(quantity('-3k'))",
		"sign(quantity('0'))",
		"quantity('1').add(quantity('500m')) == quantity('1.5')",
		"quantity('1').add(2) == quantity('3')",
		"sign(quantity('1').sub(quantity('2')))",
		"sign(quantity('5').sub(5))",
		"quantity('1').isInteger()",
		"quantity('1000m').isInteger()",
		"quantity('1.5').isInteger()",
		"quantity('1e30').isInteger()",
		"quantity('1E').asInteger()",
		"quantity('1k').asInteger()",
		"quantity('0.5n') == quantity('1n')",
		"quantity('250m').asApproximateFloat()",
		"isQuantity('1Gi')",
		"isQuantity('1.5.5')",
		"isQuantity('')",
		// IP addresses.
		"ip('10.0.0.1') == ip('10.0.0.1')",
		"ip('10.0.0.1') == ip('10.0.0.2')",
		"ip('::1') == ip('0:0:0:0:0:0:0:1')",
		"ip('10.0.0.1').family()",
		"ip('fe80::1').family()",
		"ip('127.0.0.1').isLoopback()",
		"ip('128.0.0.1').isLoopback()",
		"ip('::1').isLoopback()",
		"ip('::2').isLoopback()",
		"ip('0.0.0.0').isUnspecified()",
		"ip('::').isUnspecified()",
		"ip('::1').isUnspecified()",
		"ip('224.0.0.1').isLinkLocalMulticast()",
		"ip('224.0.1.1').isLinkLocalMulticast()",
		"ip('ff02::1').isLinkLocalMulticast()",
		"ip('ff12::1').isLinkLocalMulticast()",
		"ip('ff05::1').isLinkLocalMulticast()",
		"ip('169.254.1.1').isLinkLocalUnicast()",
		"ip('fe80::1').isLinkLocalUnicast()",
		"ip('febf::1').isLinkLocalUnicast()",
		"ip('fec0::1').isLinkLocalUnicast()",
		"ip('8.8.8.8').isGlobalUnicast()",
		"ip('255.255.255.255').isGlobalUnicast()",
		"ip('224.0.0.1').isGlobalUnicast()",
		"ip('2001:db8::1').isGlobalUnicast()",
		"ip('ff00::1').isGlobalUnicast()",
		"isIP('1.2.3.4')",
		"isIP('1.2.3')",
		"isIP('::ffff:1.2.3.4')",
		"isIP('fe80::1%eth0')",
		"ip.isCanonical('2001:db8::1')",
		"ip.isCanonical('2001:DB8::1')",
		// CIDRs.
		"cidr('10.0.0.0/8').containsIP(ip('10.1.2.3'))",
		"cidr('10.0.0.0/8').containsIP(ip('11.1.2.3'))",
		"cidr('10.0.0.0/8').containsIP('10.255.255.255')",
		"cidr('10.0.0.0/8').containsIP(ip('::a00:1'))",
		"cidr('2001:db8::/32').containsIP('2001:db8:1::1')",
		"cidr('2001:db8::/32').containsIP('2001:db9::1')",
		"cidr('0.0.0.0/0').containsIP('1.2.3.4')",
		"cidr('10.0.0.0/8').containsCIDR(cidr('10.1.0.0/16'))",
		"cidr('10.1.0.0/16').containsCIDR(cidr('10.0.0.0/8'))",
		"cidr('10.0.0.0/8').containsCIDR('10.0.0.0/8')",
		"cidr('10.0.0.0/8').containsCIDR('11.0.0.0/16')",
		"cidr('10.0.0.1/8').ip() == ip('10.0.0.1')",
		"cidr('10.0.0.1/8').masked() == cidr('10.0.0.0/8')",
		"cidr('10.0.0.1/8') == cidr('10.0.0.0/8')",
		"cidr('2001:db8::1/64').masked() == cidr('2001:db8::/64')",
		"cidr('10.0.0.0/8').prefixLength()",
		"isCIDR('10.0.0.0/8')",
		"isCIDR('10.0.0.0/33')",
		// Semantic versions.
		"semver('1.2.3') == semver('1.2.3+build')",
		"semver('1.2.3').major()",
		"semver('1.2.3').minor()",
		"semver('1.2.3').patch()",
		"semver('1.2.3').isGreaterThan(semver('1.2.2'))",
		"semver('1.10.0').isGreaterThan(semver('1.9.0'))",
		"semver('1.0.0').isGreaterThan(semver('1.0.0-alpha'))",
		"semver('1.0.0-alpha').isLessThan(semver('1.0.0'))",
		"semver('2.0.0').compareTo(semver('1.99.99'))",
		"semver('1.0.0-rc.1').compareTo(semver('1.0.0-rc.1'))",
		"isSemver('1.2.3')",
		"isSemver('v1.2')",
		"isSemver('v1.2', true)",
		"semver('v1.2', true) == semver('1.2.0')",
		// Named formats.
		"format.dns1123Label() == format.dns1123Label()",
		"format.dns1123Label() == format.dns1123Subdomain()",
		"format.named('dns1123Label') == optional.of(format.dns1123Label())",
		"format.named('nope').hasValue()",
		// Lists.
		"[1, 2, 3].isSorted()",
		"[1, 3, 2].isSorted()",
		"['a', 'b', 'b'].isSorted()",
		"[true, false].isSorted()",
		"[3, 1, 2].max()",
		"[3, 1, 2].min()",
		"['b', 'c', 'a'].max()",
		"[1u, 5u].sum()",
		"[1, 2, 3].sum()",
		"[1.5, 2.5].sum()",
		"int([timestamp(3) - timestamp(2), timestamp(5) - timestamp(3)].sum())",
		"[1, 2, 1].indexOf(1)",
		"[1, 2, 1].lastIndexOf(1)",
		"[1, 2, 1].indexOf(3)",
		"['a', 'b'].lastIndexOf('b')",
	}
	env := newEnv(t)
	v := newVerifier(t, env)
	for _, expr := range exprs {
		t.Run(expr, func(t *testing.T) {
			a := compile(t, env, expr)
			prg, err := env.Program(a)
			if err != nil {
				t.Fatal(err)
			}
			want, _, err := prg.Eval(cel.NoVars())
			if err != nil {
				t.Fatalf("runtime: %v", err)
			}
			lit := literal(t, want)
			check := compile(t, env, "("+expr+") == "+lit)
			r, err := v.IsAlwaysTrue(check)
			if err != nil {
				t.Fatal(err)
			}
			if r.Status != verifier.Verified {
				t.Errorf("runtime gives %s, but the verifier says %v: %s", lit, r.Status, r.Message())
			}
		})
	}
}

// literal renders a runtime value as a CEL expression.
func literal(t *testing.T, v any) string {
	switch v := v.(type) {
	case types.Bool:
		if v {
			return "true"
		}
		return "false"
	case types.Int:
		return v.ConvertToType(types.StringType).(types.String).Value().(string)
	case types.Uint:
		return v.ConvertToType(types.StringType).(types.String).Value().(string) + "u"
	case types.Double:
		s := strconv.FormatFloat(float64(v), 'g', -1, 64)
		if !strings.ContainsAny(s, ".e") {
			s += ".0"
		}
		return s
	case types.String:
		return "'" + string(v) + "'"
	case types.Duration:
		return "duration('" + v.ConvertToType(types.StringType).(types.String).Value().(string) + "')"
	}
	t.Fatalf("no literal for %T", v)
	return ""
}

// TestProperties proves general properties of the libraries over all inputs.
func TestProperties(t *testing.T) {
	requireZ3(t)
	env := newEnv(t,
		cel.Variable("s", cel.StringType), cel.Variable("u", cel.StringType),
		cel.Variable("n", cel.IntType),
		cel.Variable("l", cel.ListType(cel.IntType)), cel.Variable("x", cel.IntType),
		cel.Variable("names", cel.ListType(cel.StringType)))
	v := newVerifier(t, env)
	for _, tc := range []struct {
		expr string
		want verifier.Status
	}{
		// Quantities: the arithmetic and order are exact.
		{"!isQuantity(s) || !isQuantity(u) || quantity(s).add(quantity(u)).sub(quantity(u)) == quantity(s)", verifier.Verified},
		{"!isQuantity(s) || !isQuantity(u) || quantity(s).isGreaterThan(quantity(u)) == quantity(u).isLessThan(quantity(s))", verifier.Verified},
		{"!isQuantity(s) || sign(quantity(s)) in [-1, 0, 1]", verifier.Verified},
		{"!isQuantity(s) || quantity(s).add(n).compareTo(quantity(s)) == (n > 0 ? 1 : n < 0 ? -1 : 0)", verifier.Verified},
		{"!isQuantity(s) || !quantity(s).isInteger() || quantity(s).asInteger() == quantity(s).asInteger()", verifier.Verified},
		{"!isQuantity(s) || quantity(s).isLessThan(quantity('1Gi'))", verifier.Inconclusive},
		// A conversion fails exactly when the matching test is false.
		// Showing the failure needs an invalid quantity, which the uninterpreted conversion can only suggest.
		{"isQuantity(s) || sign(quantity(s)) == 0", verifier.Inconclusive},
		{"isQuantity('1x') || sign(quantity('1x')) == 0", verifier.Violated},
		{"isIP(s) == ip.isCanonical(s) || !isIP(s) || true", verifier.Verified},
		// CIDR containment is transitive and agrees with masking.
		{"!isIP(s) || !cidr('10.1.0.0/16').containsIP(s) || cidr('10.0.0.0/8').containsIP(s)", verifier.Verified},
		{"!isIP(s) || !cidr('10.0.0.0/8').containsIP(s) || cidr('10.1.0.0/16').containsIP(s)", verifier.Inconclusive},
		{"!isCIDR(s) || cidr(s).containsCIDR(cidr(s))", verifier.Verified},
		{"!isCIDR(s) || cidr(s).containsIP(cidr(s).ip())", verifier.Verified},
		{"!isCIDR(s) || cidr(s).masked().containsCIDR(cidr(s))", verifier.Verified},
		{"!isIP(s) || !ip(s).isLoopback() || !ip(s).isGlobalUnicast()", verifier.Verified},
		{"!isIP(s) || ip(s).family() == 4 || ip(s).family() == 6", verifier.Verified},
		{"!isIP(s) || !ip(s).isLinkLocalUnicast() || !cidr('10.0.0.0/8').containsIP(ip(s))", verifier.Verified},
		// Semantic versions.
		{"!isSemver(s) || !isSemver(u) || semver(s).isGreaterThan(semver(u)) == semver(u).isLessThan(semver(s))", verifier.Verified},
		{"!isSemver(s) || !isSemver(u) || semver(s).compareTo(semver(u)) == -semver(u).compareTo(semver(s))", verifier.Verified},
		{"!isSemver(s) || semver(s).major() >= 0", verifier.Verified},
		{"!isSemver(s) || !semver(s).isGreaterThan(semver('1.0.0')) || semver(s).major() >= 1", verifier.Verified},
		// Formats.
		{"format.named(s).hasValue() == (s in ['dns1123Label', 'dns1123Subdomain', 'dns1035Label', 'qualifiedName', 'dns1123LabelPrefix', 'dns1123SubdomainPrefix', 'dns1035LabelPrefix', 'labelValue', 'uri', 'uuid', 'byte', 'date', 'datetime'])", verifier.Verified},
		{"!format.named(s).hasValue() || format.named(s).value().validate(u) == format.named(s).value().validate(u)", verifier.Verified},
		// Lists: exact up to the unroll limit.
		{"size(l) == 0 || size(l) > 5 || l.min() <= l.max()", verifier.Verified},
		{"size(l) < 2 || size(l) > 5 || !l.isSorted() || l[0] <= l[1]", verifier.Verified},
		{"size(l) > 5 || l.indexOf(x) <= l.lastIndexOf(x)", verifier.Verified},
		{"size(l) > 5 || l.indexOf(x) == -1 || l[l.indexOf(x)] == x", verifier.Verified},
		// Both sides overflow to errors for e.g. [-1, -9223372036854775808].
		{"size(l) != 2 || l.sum() == l[0] + l[1]", verifier.Violated},
		{"size(l) != 2 || l[0] < 0 || l[1] < 0 || l[0] > 1000 || l[1] > 1000 || l.sum() == l[0] + l[1]", verifier.Verified},
		{"size(l) == 0 || l.sum() >= l.max()", verifier.Violated},
		{"names.isSorted() || names.size() >= 2", verifier.Verified},
		{"size(l) == 0 || l.min() <= l.max()", verifier.Inconclusive},
		// Beyond the unroll limit nothing is assumed.
		{"l.lastIndexOf(x) < 5", verifier.Inconclusive},
	} {
		t.Run(tc.expr, func(t *testing.T) {
			r, err := v.IsAlwaysTrue(compile(t, env, tc.expr))
			if err != nil {
				t.Fatal(err)
			}
			if r.Status != tc.want {
				t.Errorf("got %v, want %v: %s", r.Status, tc.want, r.Message())
			}
		})
	}
}

// TestAuthorizer shows that authorizer checks are deterministic: the same
// check always has the same outcome, but nothing else is assumed.
func TestAuthorizer(t *testing.T) {
	requireZ3(t)
	env := newEnv(t, cel.Variable("authorizer", library.AuthorizerType), cel.Variable("verb", cel.StringType))
	v := newVerifier(t, env)
	check := "authorizer.group('apps').resource('deployments').namespace('default').check('create').allowed()"
	for _, tc := range []struct {
		a, b string
		want verifier.Status
	}{
		{check, check, verifier.Verified},
		{check, strings.Replace(check, "'create'", "verb", 1) + " || verb != 'create'", verifier.Inconclusive},
		{"verb == 'create' && " + check, "verb == 'create' && " + strings.Replace(check, "'create'", "verb", 1), verifier.Verified},
		{check, strings.Replace(check, "'create'", "'delete'", 1), verifier.Inconclusive},
	} {
		t.Run(tc.b, func(t *testing.T) {
			r, err := v.VerifyEquivalence(compile(t, env, tc.a), compile(t, env, tc.b))
			if err != nil {
				t.Fatal(err)
			}
			if r.Status != tc.want {
				t.Errorf("got %v, want %v: %s", r.Status, tc.want, r.Message())
			}
		})
	}
}

// TestWitnessDisplay checks that counterexamples show library values the way they're written.
func TestWitnessDisplay(t *testing.T) {
	requireZ3(t)
	env := newEnv(t, cel.Variable("l", cel.ListType(cel.IntType)))
	v := newVerifier(t, env)
	r, err := v.IsAlwaysTrue(compile(t, env, "size(l) == 0 || l.sum() >= l.max()"))
	if err != nil {
		t.Fatal(err)
	}
	if r.Status != verifier.Violated || !strings.Contains(r.Message(), "l = [") {
		t.Errorf("got %v: %s", r.Status, r.Message())
	}
	r, err = v.IsSatisfiable(compile(t, env, "cidr('10.0.0.0/8').masked() == cidr('10.0.0.0/8') && l.max() == 3"))
	if err != nil {
		t.Fatal(err)
	}
	if r.Status != verifier.Verified {
		t.Errorf("got %v: %s", r.Status, r.Message())
	}
}

// TestCounterexamplesReplay checks that counterexamples over the libraries'
// types are real: the runtime evaluates the expression to false on them.
func TestCounterexamplesReplay(t *testing.T) {
	requireZ3(t)
	env := newEnv(t,
		cel.Variable("addr", apiservercel.IPType), cel.Variable("net", apiservercel.CIDRType),
		cel.Variable("q", apiservercel.QuantityType), cel.Variable("ver", apiservercel.SemverType),
		cel.Variable("l", cel.ListType(cel.IntType)))
	v := newVerifier(t, env)
	for _, expr := range []string{
		"!cidr('10.0.0.0/8').containsIP(addr)",
		"!net.containsIP(addr) || addr.family() == 4",
		"addr.isLoopback() || !addr.isGlobalUnicast()",
		"!net.containsCIDR(cidr('192.168.0.0/16'))",
		"net.masked() == net",
		"q.isLessThan(quantity('1Gi'))",
		"q.add(quantity('500m')).isGreaterThan(quantity('2'))",
		"ver.isLessThan(semver('1.2.3'))",
		"ver.major() < 2 || ver.minor() > 0",
		"size(l) == 0 || size(l) > 4 || l.sum() >= l.max()",
		"l.isSorted() || l.indexOf(3) != 1",
	} {
		t.Run(expr, func(t *testing.T) {
			a := compile(t, env, expr)
			r, err := v.IsAlwaysTrue(a)
			if err != nil {
				t.Fatal(err)
			}
			if r.Status != verifier.Violated || r.Witness == nil {
				t.Fatalf("got %v: %s", r.Status, r.Message())
			}
			act := map[string]any{}
			for name, wv := range r.Witness.Variables {
				if wv.Value == nil {
					t.Fatalf("inexact witness for %s: %s", name, wv.Display)
				}
				act[name] = wv.Value
			}
			prg, err := env.Program(a)
			if err != nil {
				t.Fatal(err)
			}
			out, _, err := prg.Eval(act)
			if err == nil && out == types.True {
				t.Errorf("the runtime evaluates %s to true on the counterexample:%s", expr, r.Message())
			}
		})
	}
}
