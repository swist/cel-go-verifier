package kube

import (
	"fmt"
	"math/big"
	"strings"

	"cel.dev/cel-go/common/types"
	"cel.dev/cel-go/common/types/ref"
	"github.com/blang/semver/v4"
	apiservercel "k8s.io/apiserver/pkg/cel"

	"github.com/swist/cel-go-verifier/smt"
	"github.com/swist/cel-go-verifier/verifier"
)

// Versions are encoded by major, minor, patch and their pre-release
// identifiers joined by dots; build metadata doesn't take part in their
// equality or order. Versions are ordered exactly by their numbers and by
// whether they have a pre-release; the order of two different pre-releases is
// uninterpreted.

func defineSemver(ts *verifier.TypeSystem, sink func(*smt.Term), r, major, minor, patch, pre *smt.Term) *smt.Term {
	return ts.DefineObject(sink, r, semverType,
		verifier.ObjectField{Name: "major", Value: ts.WrapInt(major)},
		verifier.ObjectField{Name: "minor", Value: ts.WrapInt(minor)},
		verifier.ObjectField{Name: "patch", Value: ts.WrapInt(patch)},
		verifier.ObjectField{Name: "pre", Value: ts.WrapString(pre)})
}

func preRelease(v semver.Version) string {
	parts := make([]string, len(v.Pre))
	for i, p := range v.Pre {
		parts[i] = p.String()
	}
	return strings.Join(parts, ".")
}

func constSemver(c *smt.Context, ts *verifier.TypeSystem, sink func(*smt.Term), v semver.Version) *smt.Term {
	v.Build = nil
	r := constObject(c, ts, "semver:"+v.String(), v)
	return defineSemver(ts, sink, r,
		c.MkIntBig(new(big.Int).SetUint64(v.Major)), c.MkIntBig(new(big.Int).SetUint64(v.Minor)),
		c.MkIntBig(new(big.Int).SetUint64(v.Patch)), verifier.MkZ3String(c, preRelease(v)))
}

// semverConversion converts with or without normalization.
func semverConversion(normalize bool) conversion {
	suffix := ""
	if normalize {
		suffix = "_normalized"
	}
	return conversion{
		literal: func(c *smt.Context, ts *verifier.TypeSystem, sink func(*smt.Term), s string) (*smt.Term, bool) {
			v, ok := eval("semver(a, b)", types.String(s), types.Bool(normalize)).(apiservercel.Semver)
			if !ok {
				return nil, false
			}
			return constSemver(c, ts, sink, v.Version), true
		},
		symbolic: func(c *smt.Context, ts *verifier.TypeSystem, sink func(*smt.Term), s *smt.Term) (*smt.Term, *smt.Term) {
			str := c.StringSort()
			part := func(name string) *smt.Term {
				t := c.MkApp(fn(ts, "semver_"+name+suffix, c.IntSort(), str), s)
				sink(c.MkGe(t, c.MkInt(0)))
				return t
			}
			r := c.MkApp(fn(ts, "semver_of"+suffix, ts.MessageRefSort(), str), s)
			pre := c.MkApp(fn(ts, "semver_pre"+suffix, str, str), s)
			v := defineSemver(ts, sink, r, part("major"), part("minor"), part("patch"), pre)
			return v, c.MkApp(fn(ts, "is_semver"+suffix, c.BoolSort(), str), s)
		},
	}
}

// compareSemver returns the comparison of a and b as an int term, and when it's approximate.
func compareSemver(c *smt.Context, ts *verifier.TypeSystem, sink func(*smt.Term), a, b *smt.Term) (cmp, approx *smt.Term) {
	cmpInt := func(x, y *smt.Term, rest *smt.Term) *smt.Term {
		return c.MkITE(c.MkLt(x, y), c.MkInt(-1), c.MkITE(c.MkGt(x, y), c.MkInt(1), rest))
	}
	preA, preB := ts.GetString(ts.ObjectField(a, "pre")), ts.GetString(ts.ObjectField(b, "pre"))
	empty := verifier.MkZ3String(c, "")
	noneA, noneB := c.MkEq(preA, empty), c.MkEq(preB, empty)
	// Different pre-releases compare by rules (numeric and alphanumeric
	// identifiers) left uninterpreted, as an antisymmetric order.
	order := fn(ts, "semver_pre_less", c.BoolSort(), c.StringSort(), c.StringSort())
	lessAB, lessBA := c.MkApp(order, preA, preB), c.MkApp(order, preB, preA)
	differ := c.MkNot(c.MkEq(preA, preB))
	pre := c.MkITE(c.MkEq(preA, preB), c.MkInt(0),
		c.MkITE(noneA, c.MkInt(1),
			c.MkITE(noneB, c.MkInt(-1),
				c.MkITE(lessAB, c.MkInt(-1), c.MkInt(1)))))
	// The uninterpreted order is consistent: of two different pre-releases exactly one is less.
	sink(c.MkImplies(differ, c.MkXor(lessAB, lessBA)))
	major := func(v *smt.Term) *smt.Term { return intField(ts, v, "major") }
	minor := func(v *smt.Term) *smt.Term { return intField(ts, v, "minor") }
	patch := func(v *smt.Term) *smt.Term { return intField(ts, v, "patch") }
	numbersEqual := c.MkAnd(c.MkEq(major(a), major(b)), c.MkEq(minor(a), minor(b)), c.MkEq(patch(a), patch(b)))
	cmp = cmpInt(major(a), major(b), cmpInt(minor(a), minor(b), cmpInt(patch(a), patch(b), pre)))
	approx = c.MkAnd(numbersEqual, differ, c.MkNot(noneA), c.MkNot(noneB))
	return cmp, approx
}

func semverAxioms() []*verifier.FunctionAxiom {
	conv := newAxiom("semver")
	unaryOverload(conv, "string_to_semver", semverConversion(false).translate)
	binaryOverload(conv, "string_bool_to_semver", func(c *smt.Context, ts *verifier.TypeSystem, sink func(*smt.Term), s, normalize *smt.Term) (*smt.Term, *smt.Term) {
		if n, ok := ts.BoolLiteral(normalize); ok {
			return semverConversion(n).translate(c, ts, sink, s)
		}
		v1, a1 := semverConversion(false).translate(c, ts, sink, s)
		v2, a2 := semverConversion(true).translate(c, ts, sink, s)
		return c.MkITE(ts.UnwrapBool(normalize), v2, v1), c.MkOr(a1, a2)
	})
	isSemver := newAxiom("isSemver")
	unaryOverload(isSemver, "is_semver_string", semverConversion(false).validity)
	binaryOverload(isSemver, "is_semver_string_bool", func(c *smt.Context, ts *verifier.TypeSystem, sink func(*smt.Term), s, normalize *smt.Term) (*smt.Term, *smt.Term) {
		if n, ok := ts.BoolLiteral(normalize); ok {
			return semverConversion(n).validity(c, ts, sink, s)
		}
		v1, a1 := semverConversion(false).validity(c, ts, sink, s)
		v2, a2 := semverConversion(true).validity(c, ts, sink, s)
		return c.MkITE(ts.UnwrapBool(normalize), v2, v1), c.MkOr(a1, a2)
	})

	compare := func(f func(c *smt.Context, ts *verifier.TypeSystem, cmp *smt.Term) *smt.Term) func(c *smt.Context, ts *verifier.TypeSystem, sink func(*smt.Term), a, b *smt.Term) (*smt.Term, *smt.Term) {
		return func(c *smt.Context, ts *verifier.TypeSystem, sink func(*smt.Term), a, b *smt.Term) (*smt.Term, *smt.Term) {
			cmp, approx := compareSemver(c, ts, sink, a, b)
			return f(c, ts, cmp), approx
		}
	}
	gt := newAxiom("isGreaterThan")
	binaryOverload(gt, "semver_is_greater_than", compare(func(c *smt.Context, ts *verifier.TypeSystem, cmp *smt.Term) *smt.Term {
		return ts.WrapBool(c.MkEq(cmp, c.MkInt(1)))
	}))
	lt := newAxiom("isLessThan")
	binaryOverload(lt, "semver_is_less_than", compare(func(c *smt.Context, ts *verifier.TypeSystem, cmp *smt.Term) *smt.Term {
		return ts.WrapBool(c.MkEq(cmp, c.MkInt(-1)))
	}))
	compareTo := newAxiom("compareTo")
	binaryOverload(compareTo, "semver_compare_to", compare(func(c *smt.Context, ts *verifier.TypeSystem, cmp *smt.Term) *smt.Term {
		return ts.WrapInt(cmp)
	}))
	part := func(name, id string) *verifier.FunctionAxiom {
		return newAxiom(name).Unary(id, func(c *smt.Context, ts *verifier.TypeSystem, _ func(*smt.Term), v *smt.Term) (*smt.Term, bool) {
			return ts.ObjectField(v, name), true
		}, false)
	}
	return []*verifier.FunctionAxiom{conv, isSemver, gt, lt, compareTo,
		part("major", "semver_major"), part("minor", "semver_minor"), part("patch", "semver_patch")}
}

func formatSemver(fields map[string]verifier.MessageField) (ref.Val, string, bool) {
	var nums [3]uint64
	for i, name := range []string{"major", "minor", "patch"} {
		n, ok := verifier.BigIntField(fields[name])
		if !ok || !n.IsUint64() {
			return nil, "", false
		}
		nums[i] = n.Uint64()
	}
	s := fmt.Sprintf("%d.%d.%d", nums[0], nums[1], nums[2])
	if pre, ok := fields["pre"].Value.(types.String); ok && pre != "" {
		s += "-" + string(pre)
	}
	v, err := semver.Parse(s)
	if err != nil {
		return nil, fmt.Sprintf("semver('%s')", s), true
	}
	return apiservercel.Semver{Version: v}, fmt.Sprintf("semver('%s')", s), true
}
