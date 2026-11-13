package kube

import (
	"fmt"
	"math/big"
	"net/netip"

	"cel.dev/cel-go/common/types"
	"cel.dev/cel-go/common/types/ref"
	apiservercel "k8s.io/apiserver/pkg/cel"

	"github.com/swist/cel-go-verifier/smt"
	"github.com/swist/cel-go-verifier/verifier"
)

// IP addresses are encoded by their family and their address as an unsigned
// integer (32 bits for IPv4, 128 for IPv6); CIDRs also by their prefix
// length, with the address as written (cidr('10.0.0.1/8') keeps the host
// bits). The library rejects zones and IPv4-mapped IPv6 addresses, so these
// determine the values.

func addrInt(a netip.Addr) *big.Int { b := a.AsSlice(); return new(big.Int).SetBytes(b) }

func intAddr(family int64, n *big.Int) (netip.Addr, bool) {
	size := 4
	if family == 6 {
		size = 16
	}
	if n.Sign() < 0 || n.BitLen() > size*8 {
		return netip.Addr{}, false
	}
	b := n.FillBytes(make([]byte, size))
	a, ok := netip.AddrFromSlice(b)
	return a, ok
}

func familyOf(a netip.Addr) int64 {
	if a.Is4() {
		return 4
	}
	return 6
}

func pow2(n int) *big.Int { return new(big.Int).Lsh(big.NewInt(1), uint(n)) }

// bits returns the address size of the family term: 32 or 128.
func addressBits(c *smt.Context, family *smt.Term) *smt.Term {
	return c.MkITE(c.MkEq(family, c.MkInt(4)), c.MkInt(32), c.MkInt(128))
}

func defineIP(ts *verifier.TypeSystem, sink func(*smt.Term), r, family, addr *smt.Term) *smt.Term {
	return ts.DefineObject(sink, r, ipType,
		verifier.ObjectField{Name: "family", Value: ts.WrapInt(family)},
		verifier.ObjectField{Name: "addr", Value: ts.WrapInt(addr)})
}

func defineCIDR(ts *verifier.TypeSystem, sink func(*smt.Term), r, family, addr, prefix *smt.Term) *smt.Term {
	return ts.DefineObject(sink, r, cidrType,
		verifier.ObjectField{Name: "family", Value: ts.WrapInt(family)},
		verifier.ObjectField{Name: "addr", Value: ts.WrapInt(addr)},
		verifier.ObjectField{Name: "prefix", Value: ts.WrapInt(prefix)})
}

// wellFormed constrains a family and an address (and a prefix length) to a valid combination.
func wellFormed(c *smt.Context, family, addr, prefix *smt.Term) *smt.Term {
	is4 := c.MkEq(family, c.MkInt(4))
	parts := []*smt.Term{
		c.MkOr(is4, c.MkEq(family, c.MkInt(6))),
		c.MkGe(addr, c.MkInt(0)),
		c.MkLt(addr, c.MkITE(is4, c.MkIntBig(pow2(32)), c.MkIntBig(pow2(128)))),
	}
	if prefix != nil {
		parts = append(parts, c.MkGe(prefix, c.MkInt(0)), c.MkLe(prefix, addressBits(c, family)))
	}
	return c.MkAnd(parts...)
}

func constIP(c *smt.Context, ts *verifier.TypeSystem, sink func(*smt.Term), a netip.Addr) *smt.Term {
	r := constObject(c, ts, "ip:"+a.String(), a)
	return defineIP(ts, sink, r, c.MkInt(familyOf(a)), c.MkIntBig(addrInt(a)))
}

func constCIDR(c *smt.Context, ts *verifier.TypeSystem, sink func(*smt.Term), p netip.Prefix) *smt.Term {
	r := constObject(c, ts, "cidr:"+p.String(), p)
	return defineCIDR(ts, sink, r, c.MkInt(familyOf(p.Addr())), c.MkIntBig(addrInt(p.Addr())), c.MkInt(int64(p.Bits())))
}

var ipConversion = conversion{
	literal: func(c *smt.Context, ts *verifier.TypeSystem, sink func(*smt.Term), s string) (*smt.Term, bool) {
		v, ok := eval("ip(a)", types.String(s)).(apiservercel.IP)
		if !ok {
			return nil, false
		}
		return constIP(c, ts, sink, v.Addr), true
	},
	symbolic: func(c *smt.Context, ts *verifier.TypeSystem, sink func(*smt.Term), s *smt.Term) (*smt.Term, *smt.Term) {
		str := c.StringSort()
		r := c.MkApp(fn(ts, "ip_of", ts.MessageRefSort(), str), s)
		family := c.MkApp(fn(ts, "ip_family", c.IntSort(), str), s)
		addr := c.MkApp(fn(ts, "ip_addr", c.IntSort(), str), s)
		sink(wellFormed(c, family, addr, nil))
		return defineIP(ts, sink, r, family, addr), c.MkApp(fn(ts, "is_ip", c.BoolSort(), str), s)
	},
}

var cidrConversion = conversion{
	literal: func(c *smt.Context, ts *verifier.TypeSystem, sink func(*smt.Term), s string) (*smt.Term, bool) {
		v, ok := eval("cidr(a)", types.String(s)).(apiservercel.CIDR)
		if !ok {
			return nil, false
		}
		return constCIDR(c, ts, sink, v.Prefix), true
	},
	symbolic: func(c *smt.Context, ts *verifier.TypeSystem, sink func(*smt.Term), s *smt.Term) (*smt.Term, *smt.Term) {
		str := c.StringSort()
		r := c.MkApp(fn(ts, "cidr_of", ts.MessageRefSort(), str), s)
		family := c.MkApp(fn(ts, "cidr_family", c.IntSort(), str), s)
		addr := c.MkApp(fn(ts, "cidr_addr", c.IntSort(), str), s)
		prefix := c.MkApp(fn(ts, "cidr_prefix", c.IntSort(), str), s)
		sink(wellFormed(c, family, addr, prefix))
		return defineCIDR(ts, sink, r, family, addr, prefix), c.MkApp(fn(ts, "is_cidr", c.BoolSort(), str), s)
	},
}

// inRange tests whether addr (of family) lies in the network of the given
// constant prefix, e.g. 127.0.0.0/8.
func inRange(c *smt.Context, family, addr *smt.Term, network string) *smt.Term {
	p := netip.MustParsePrefix(network)
	size := p.Addr().BitLen()
	unit := c.MkIntBig(pow2(size - p.Bits()))
	return c.MkAnd(c.MkEq(family, c.MkInt(familyOf(p.Addr()))),
		c.MkEq(c.MkDiv(addr, unit), c.MkIntBig(new(big.Int).Div(addrInt(p.Addr()), pow2(size-p.Bits())))))
}

// samePrefix tests whether two addresses of a family agree on the first
// prefix bits. A constant prefix keeps the arithmetic linear; otherwise each
// possible length is a case.
func samePrefix(c *smt.Context, family, a, b, prefix *smt.Term, constPrefix int, constFamily int64) *smt.Term {
	agree := func(size, bits int) *smt.Term {
		unit := c.MkIntBig(pow2(size - bits))
		return c.MkEq(c.MkDiv(a, unit), c.MkDiv(b, unit))
	}
	if constPrefix >= 0 {
		return agree(map[int64]int{4: 32, 6: 128}[constFamily], constPrefix)
	}
	var cases []*smt.Term
	for _, fam := range []struct {
		f    int64
		size int
	}{{4, 32}, {6, 128}} {
		for k := 0; k <= fam.size; k++ {
			cases = append(cases, c.MkAnd(c.MkEq(family, c.MkInt(fam.f)), c.MkEq(prefix, c.MkInt(int64(k))), agree(fam.size, k)))
		}
	}
	return c.MkOr(cases...)
}

// maskedAddr clears the host bits of an address.
func maskedAddr(c *smt.Context, family, addr, prefix *smt.Term, constPrefix int, constFamily int64) *smt.Term {
	mask := func(size, bits int) *smt.Term {
		unit := c.MkIntBig(pow2(size - bits))
		return c.MkSub(addr, c.MkMod(addr, unit))
	}
	if constPrefix >= 0 {
		return mask(map[int64]int{4: 32, 6: 128}[constFamily], constPrefix)
	}
	out := addr
	for _, fam := range []struct {
		f    int64
		size int
	}{{4, 32}, {6, 128}} {
		for k := 0; k <= fam.size; k++ {
			out = c.MkITE(c.MkAnd(c.MkEq(family, c.MkInt(fam.f)), c.MkEq(prefix, c.MkInt(int64(k)))), mask(fam.size, k), out)
		}
	}
	return out
}

// cidrParts returns the representation of a CIDR, with its prefix length and family if constant (else -1, 0).
func cidrParts(ts *verifier.TypeSystem, v *smt.Term) (family, addr, prefix *smt.Term, constPrefix int, constFamily int64) {
	family, addr, prefix = intField(ts, v, "family"), intField(ts, v, "addr"), intField(ts, v, "prefix")
	if k, ok := constantOf(ts, v); ok {
		p := k.(netip.Prefix)
		return family, addr, prefix, p.Bits(), familyOf(p.Addr())
	}
	return family, addr, prefix, -1, 0
}

func ipAxioms() []*verifier.FunctionAxiom {
	ipFn := newAxiom("ip")
	unaryOverload(ipFn, "string_to_ip", ipConversion.translate)
	ipFn.Unary("cidr_ip", func(c *smt.Context, ts *verifier.TypeSystem, sink func(*smt.Term), v *smt.Term) (*smt.Term, bool) {
		family, addr, _, _, _ := cidrParts(ts, v)
		r := c.MkApp(fn(ts, "cidr_ip", ts.MessageRefSort(), ts.CelValueSort()), v)
		return defineIP(ts, sink, r, family, addr), true
	}, false)
	isIP := newAxiom("isIP")
	unaryOverload(isIP, "is_ip", ipConversion.validity)
	isCanonical := newAxiom("ip.isCanonical")
	unaryOverload(isCanonical, "ip_is_canonical", func(c *smt.Context, ts *verifier.TypeSystem, sink func(*smt.Term), arg *smt.Term) (*smt.Term, *smt.Term) {
		if s, ok := ts.StringLiteral(arg); ok {
			if b, ok := eval("ip.isCanonical(a)", types.String(s)).(types.Bool); ok {
				return ts.MkBool(bool(b)), c.MkFalse()
			}
			return ts.MkError(), c.MkFalse()
		}
		str := ts.GetString(arg)
		valid := c.MkApp(fn(ts, "is_ip", c.BoolSort(), c.StringSort()), str)
		canonical := c.MkApp(fn(ts, "ip_is_canonical", c.BoolSort(), c.StringSort()), str)
		return c.MkITE(valid, ts.WrapBool(canonical), ts.MkError()), c.MkTrue()
	})

	family := newAxiom("family").Unary("ip_family", func(c *smt.Context, ts *verifier.TypeSystem, _ func(*smt.Term), v *smt.Term) (*smt.Term, bool) {
		return ts.WrapInt(intField(ts, v, "family")), true
	}, false)
	predicate := func(name, id string, f func(c *smt.Context, family, addr *smt.Term) *smt.Term) *verifier.FunctionAxiom {
		return newAxiom(name).Unary(id, func(c *smt.Context, ts *verifier.TypeSystem, _ func(*smt.Term), v *smt.Term) (*smt.Term, bool) {
			return ts.WrapBool(f(c, intField(ts, v, "family"), intField(ts, v, "addr"))), true
		}, false)
	}
	isUnspecified := func(c *smt.Context, family, addr *smt.Term) *smt.Term { return c.MkEq(addr, c.MkInt(0)) }
	isLoopback := func(c *smt.Context, family, addr *smt.Term) *smt.Term {
		return c.MkOr(inRange(c, family, addr, "127.0.0.0/8"), inRange(c, family, addr, "::1/128"))
	}
	isMulticast := func(c *smt.Context, family, addr *smt.Term) *smt.Term {
		return c.MkOr(inRange(c, family, addr, "224.0.0.0/4"), inRange(c, family, addr, "ff00::/8"))
	}
	isLinkLocalUnicast := func(c *smt.Context, family, addr *smt.Term) *smt.Term {
		return c.MkOr(inRange(c, family, addr, "169.254.0.0/16"), inRange(c, family, addr, "fe80::/10"))
	}
	isLinkLocalMulticast := func(c *smt.Context, family, addr *smt.Term) *smt.Term {
		// IPv6: ff02::/16 with any flags, i.e. the first 16 bits match ff_2.
		first16 := c.MkDiv(addr, c.MkIntBig(pow2(112)))
		v6 := c.MkAnd(c.MkEq(family, c.MkInt(6)),
			c.MkEq(c.MkDiv(first16, c.MkInt(256)), c.MkInt(0xff)),
			c.MkEq(c.MkMod(first16, c.MkInt(16)), c.MkInt(2)))
		return c.MkOr(inRange(c, family, addr, "224.0.0.0/24"), v6)
	}
	isGlobalUnicast := func(c *smt.Context, family, addr *smt.Term) *smt.Term {
		broadcast := inRange(c, family, addr, "255.255.255.255/32")
		return c.MkAnd(c.MkNot(isUnspecified(c, family, addr)), c.MkNot(broadcast),
			c.MkNot(isLoopback(c, family, addr)), c.MkNot(isMulticast(c, family, addr)),
			c.MkNot(isLinkLocalUnicast(c, family, addr)))
	}

	cidrFn := newAxiom("cidr")
	unaryOverload(cidrFn, "string_to_cidr", cidrConversion.translate)
	isCIDR := newAxiom("isCIDR")
	unaryOverload(isCIDR, "is_cidr", cidrConversion.validity)

	containsIP := func(c *smt.Context, ts *verifier.TypeSystem, cidr, ip *smt.Term) *smt.Term {
		family, addr, prefix, cp, cf := cidrParts(ts, cidr)
		return ts.WrapBool(c.MkAnd(c.MkEq(family, intField(ts, ip, "family")),
			samePrefix(c, family, addr, intField(ts, ip, "addr"), prefix, cp, cf)))
	}
	containsCIDR := func(c *smt.Context, ts *verifier.TypeSystem, cidr, other *smt.Term) *smt.Term {
		family, addr, prefix, cp, cf := cidrParts(ts, cidr)
		return ts.WrapBool(c.MkAnd(c.MkEq(family, intField(ts, other, "family")),
			c.MkLe(prefix, intField(ts, other, "prefix")),
			samePrefix(c, family, addr, intField(ts, other, "addr"), prefix, cp, cf)))
	}
	// withConverted applies op to the CIDR and the converted string argument, failing if the conversion does.
	withConverted := func(conv conversion, op func(c *smt.Context, ts *verifier.TypeSystem, cidr, other *smt.Term) *smt.Term) func(c *smt.Context, ts *verifier.TypeSystem, sink func(*smt.Term), a, b *smt.Term) (*smt.Term, *smt.Term) {
		return func(c *smt.Context, ts *verifier.TypeSystem, sink func(*smt.Term), a, b *smt.Term) (*smt.Term, *smt.Term) {
			other, approx := conv.translate(c, ts, sink, b)
			return c.MkITE(ts.IsError(other), other, op(c, ts, a, other)), approx
		}
	}
	plain := func(op func(c *smt.Context, ts *verifier.TypeSystem, cidr, other *smt.Term) *smt.Term) verifier.BinaryTranslator {
		return func(c *smt.Context, ts *verifier.TypeSystem, _ func(*smt.Term), a, b *smt.Term) (*smt.Term, bool) {
			return op(c, ts, a, b), true
		}
	}
	containsIPFn := newAxiom("containsIP").Binary("cidr_contains_ip_ip", plain(containsIP))
	binaryOverload(containsIPFn, "cidr_contains_ip_string", withConverted(ipConversion, containsIP))
	containsCIDRFn := newAxiom("containsCIDR").Binary("cidr_contains_cidr", plain(containsCIDR))
	binaryOverload(containsCIDRFn, "cidr_contains_cidr_string", withConverted(cidrConversion, containsCIDR))

	prefixLength := newAxiom("prefixLength").Unary("cidr_prefix_length", func(c *smt.Context, ts *verifier.TypeSystem, _ func(*smt.Term), v *smt.Term) (*smt.Term, bool) {
		return ts.WrapInt(intField(ts, v, "prefix")), true
	}, false)
	masked := newAxiom("masked").Unary("cidr_masked", func(c *smt.Context, ts *verifier.TypeSystem, sink func(*smt.Term), v *smt.Term) (*smt.Term, bool) {
		family, addr, prefix, cp, cf := cidrParts(ts, v)
		r := c.MkApp(fn(ts, "cidr_masked", ts.MessageRefSort(), ts.CelValueSort()), v)
		return defineCIDR(ts, sink, r, family, maskedAddr(c, family, addr, prefix, cp, cf), prefix), true
	}, false)

	return []*verifier.FunctionAxiom{
		ipFn, isIP, isCanonical, family,
		predicate("isUnspecified", "ip_is_unspecified", isUnspecified),
		predicate("isLoopback", "ip_is_loopback", isLoopback),
		predicate("isLinkLocalMulticast", "ip_is_link_local_multicast", isLinkLocalMulticast),
		predicate("isLinkLocalUnicast", "ip_is_link_local_unicast", isLinkLocalUnicast),
		predicate("isGlobalUnicast", "ip_is_global_unicast", isGlobalUnicast),
		cidrFn, isCIDR, containsIPFn, containsCIDRFn, prefixLength, masked,
	}
}

func formatIP(fields map[string]verifier.MessageField) (ref.Val, string, bool) {
	f, ok1 := verifier.BigIntField(fields["family"])
	n, ok2 := verifier.BigIntField(fields["addr"])
	if !ok1 || !ok2 {
		return nil, "", false
	}
	a, ok := intAddr(f.Int64(), n)
	if !ok {
		return nil, "", false
	}
	return apiservercel.IP{Addr: a}, fmt.Sprintf("ip('%s')", a), true
}

func formatCIDR(fields map[string]verifier.MessageField) (ref.Val, string, bool) {
	f, ok1 := verifier.BigIntField(fields["family"])
	n, ok2 := verifier.BigIntField(fields["addr"])
	bits, ok3 := verifier.BigIntField(fields["prefix"])
	if !ok1 || !ok2 || !ok3 {
		return nil, "", false
	}
	a, ok := intAddr(f.Int64(), n)
	if !ok {
		return nil, "", false
	}
	p := netip.PrefixFrom(a, int(bits.Int64()))
	if !p.IsValid() {
		return nil, "", false
	}
	return apiservercel.CIDR{Prefix: p}, fmt.Sprintf("cidr('%s')", p), true
}
