package smt

import (
	"fmt"
	"math/big"
	"strconv"
	"strings"
)

// ParseTerm parses an SMT-LIB2 term (as printed by Z3) into a term of c.
// Symbols resolve to the declarations of c; model values (Sort!val!N) to
// model value terms.
func (c *Context) ParseTerm(src string) (*Term, error) {
	e, err := ParseSExpr(src)
	if err != nil {
		return nil, err
	}
	return c.BuildTerm(e)
}

// BuildTerm converts a parsed s-expression to a term.
func (c *Context) BuildTerm(e *SExpr) (t *Term, err error) {
	defer func() {
		if r := recover(); r != nil {
			t = nil
			err = fmt.Errorf("smt: cannot build %s: %v", truncate(e.String(), 300), r)
		}
	}()
	b := &termBuilder{c: c}
	return b.build(e)
}

func truncate(s string, n int) string {
	if len(s) > n {
		return s[:n] + "..."
	}
	return s
}

type termBuilder struct {
	c      *Context
	scopes []map[string]*Term
}

func (b *termBuilder) lookup(name string) (*Term, bool) {
	for i := len(b.scopes) - 1; i >= 0; i-- {
		if t, ok := b.scopes[i][name]; ok {
			return t, true
		}
	}
	return nil, false
}

// ParseSort parses a sort expression.
func (c *Context) ParseSort(e *SExpr) (*Sort, error) {
	switch e.Kind {
	case SSymbol:
		switch e.Atom {
		case "Bool":
			return c.boolSort, nil
		case "Int":
			return c.intSort, nil
		case "Real":
			return c.realSort, nil
		case "String":
			return c.stringSort, nil
		case "RoundingMode":
			return c.rmSort, nil
		case "Unicode":
			return c.CharSort(), nil
		case "Float64":
			return c.FPSortDouble(), nil
		case "Float32":
			return c.FPSortSingle(), nil
		}
		if s := c.sortByName[e.Atom]; s != nil {
			return s, nil
		}
	case SList:
		h := e.List
		if len(h) >= 2 && h[0].IsSymbol("Seq") {
			el, err := c.ParseSort(h[1])
			if err != nil {
				return nil, err
			}
			return c.SeqSort(el), nil
		}
		if len(h) == 3 && h[0].IsSymbol("Array") {
			d, err := c.ParseSort(h[1])
			if err != nil {
				return nil, err
			}
			r, err := c.ParseSort(h[2])
			if err != nil {
				return nil, err
			}
			return c.ArraySort(d, r), nil
		}
		if len(h) >= 3 && h[0].IsSymbol("_") {
			switch {
			case h[1].IsSymbol("FloatingPoint") && len(h) == 4:
				return c.FPSort(atoi(h[2]), atoi(h[3])), nil
			case h[1].IsSymbol("BitVec"):
				return c.BVSort(atoi(h[2])), nil
			}
		}
	}
	return nil, fmt.Errorf("smt: unknown sort %s", e)
}

func atoi(e *SExpr) int {
	n, err := strconv.Atoi(e.Atom)
	if err != nil {
		panic(fmt.Sprintf("bad index %s", e))
	}
	return n
}

var rmByName = map[string]RoundingMode{
	"roundNearestTiesToEven": RNE, "RNE": RNE,
	"roundNearestTiesToAway": RNA, "RNA": RNA,
	"roundTowardPositive": RTP, "RTP": RTP,
	"roundTowardNegative": RTN, "RTN": RTN,
	"roundTowardZero": RTZ, "RTZ": RTZ,
}

func (b *termBuilder) build(e *SExpr) (*Term, error) {
	c := b.c
	switch e.Kind {
	case SNumeral:
		v, _ := new(big.Int).SetString(e.Atom, 10)
		return c.MkIntBig(v), nil
	case SDecimal:
		r, _ := new(big.Rat).SetString(e.Atom)
		return c.MkReal(r), nil
	case SString:
		return c.MkStringRunes(e.Runes), nil
	case SBinary:
		v, _ := new(big.Int).SetString(e.Atom, 2)
		return c.MkBV(v, len(e.Atom)), nil
	case SHex:
		v, _ := new(big.Int).SetString(e.Atom, 16)
		return c.MkBV(v, 4*len(e.Atom)), nil
	case SSymbol:
		return b.symbol(e.Atom)
	case SList:
		return b.list(e)
	}
	return nil, fmt.Errorf("unexpected %s", e)
}

func (b *termBuilder) symbol(name string) (*Term, error) {
	c := b.c
	if t, ok := b.lookup(name); ok {
		return t, nil
	}
	switch name {
	case "true":
		return c.trueT, nil
	case "false":
		return c.falseT, nil
	}
	if rm, ok := rmByName[name]; ok {
		return c.MkFPRoundingMode(rm), nil
	}
	for _, d := range c.declByName[name] {
		if len(d.Domain) == 0 && (d.Kind == DeclUninterpreted || d.Kind == DeclConstructor) {
			return c.MkApp(d), nil
		}
	}
	if i := strings.Index(name, "!val!"); i > 0 {
		if s := c.sortByName[name[:i]]; s != nil {
			return c.MkModelValue(name, s), nil
		}
	}
	return nil, fmt.Errorf("unknown symbol %s", name)
}

func (b *termBuilder) args(es []*SExpr) ([]*Term, error) {
	out := make([]*Term, len(es))
	for i, e := range es {
		t, err := b.build(e)
		if err != nil {
			return nil, err
		}
		out[i] = t
	}
	return out, nil
}

func (b *termBuilder) list(e *SExpr) (*Term, error) {
	c := b.c
	if len(e.List) == 0 {
		return nil, fmt.Errorf("empty list")
	}
	head := e.List[0]
	// Non-applied indexed or qualified identifiers.
	if head.IsSymbol("_") {
		return b.indexedConst(e)
	}
	if head.IsSymbol("as") {
		if len(e.List) == 3 && e.List[1].IsSymbol("seq.empty") {
			s, err := c.ParseSort(e.List[2])
			if err != nil {
				return nil, err
			}
			return c.MkEmptySeq(s), nil
		}
		return nil, fmt.Errorf("unsupported %s", e)
	}
	if head.IsSymbol("let") {
		scope := map[string]*Term{}
		for _, binding := range e.List[1].List {
			t, err := b.build(binding.List[1])
			if err != nil {
				return nil, err
			}
			scope[binding.List[0].Atom] = t
		}
		b.scopes = append(b.scopes, scope)
		defer func() { b.scopes = b.scopes[:len(b.scopes)-1] }()
		return b.build(e.List[2])
	}
	if head.IsSymbol("lambda") || head.IsSymbol("forall") || head.IsSymbol("exists") {
		scope := map[string]*Term{}
		var vars []*Term
		for _, v := range e.List[1].List {
			s, err := c.ParseSort(v.List[1])
			if err != nil {
				return nil, err
			}
			bv := c.MkBoundVar(v.List[0].Atom, s)
			scope[v.List[0].Atom] = bv
			vars = append(vars, bv)
		}
		b.scopes = append(b.scopes, scope)
		body, err := b.build(e.List[2])
		b.scopes = b.scopes[:len(b.scopes)-1]
		if err != nil {
			return nil, err
		}
		if head.IsSymbol("lambda") {
			return c.MkLambda(vars, body), nil
		}
		return c.MkQuantifier(head.IsSymbol("forall"), vars, body), nil
	}
	args, err := b.args(e.List[1:])
	if err != nil {
		return nil, err
	}
	if head.Kind == SList {
		return b.indexedApp(head, args)
	}
	if head.Kind != SSymbol {
		return nil, fmt.Errorf("bad head %s", head)
	}
	name := head.Atom
	if t, ok := b.builtin(name, args); ok {
		return t, nil
	}
	if _, ok := b.lookup(name); !ok {
		for _, d := range c.declByName[name] {
			if d.Kind == DeclTester || len(d.Domain) != len(args) {
				continue
			}
			match := true
			for i, a := range args {
				if a.Sort != d.Domain[i] {
					match = false
				}
			}
			if match {
				return c.MkApp(d, args...), nil
			}
		}
	}
	return nil, fmt.Errorf("unknown function %s", name)
}

func (b *termBuilder) indexedConst(e *SExpr) (*Term, error) {
	c := b.c
	l := e.List
	if len(l) == 3 && l[1].IsSymbol("as-array") {
		for _, d := range c.declByName[l[2].Atom] {
			return c.MkAsArray(d), nil
		}
		return nil, fmt.Errorf("unknown as-array function %s", l[2].Atom)
	}
	if len(l) == 3 && l[1].IsSymbol("Char") {
		v, _ := new(big.Int).SetString(l[2].Atom, 10)
		return c.intern(&Term{Op: OpCharLit, Sort: c.CharSort(), Int: v}), nil
	}
	if len(l) == 3 && strings.HasPrefix(l[1].Atom, "bv") {
		v, _ := new(big.Int).SetString(l[1].Atom[2:], 10)
		return c.MkBV(v, atoi(l[2])), nil
	}
	if len(l) == 4 {
		s := c.FPSort(atoi(l[2]), atoi(l[3]))
		eb, sb := uint(s.EBits), uint(s.SBits)
		expMax := uint64(1)<<eb - 1
		switch l[1].Atom {
		case "+zero":
			return c.MkFPBits(0, s), nil
		case "-zero":
			return c.MkFPBits(uint64(1)<<(eb+sb-1), s), nil
		case "+oo":
			return c.MkFPBits(expMax<<(sb-1), s), nil
		case "-oo":
			return c.MkFPBits(uint64(1)<<(eb+sb-1)|expMax<<(sb-1), s), nil
		case "NaN":
			return c.MkFPNaN(s), nil
		}
	}
	return nil, fmt.Errorf("unsupported %s", e)
}

func (b *termBuilder) indexedApp(head *SExpr, args []*Term) (*Term, error) {
	c := b.c
	l := head.List
	if len(l) == 3 && l[0].IsSymbol("_") && l[1].IsSymbol("is") {
		for _, d := range c.declByName[l[2].Atom] {
			if d.Kind == DeclConstructor && len(args) == 1 && args[0].Sort == d.Range {
				return c.MkApp(d.Cons.Tester, args...), nil
			}
		}
		return nil, fmt.Errorf("unknown constructor %s", l[2].Atom)
	}
	if len(l) == 3 && l[0].IsSymbol("as") && l[1].IsSymbol("const") {
		s, err := c.ParseSort(l[2])
		if err != nil {
			return nil, err
		}
		return c.MkConstArray(s.Domain(), args[0]), nil
	}
	if len(l) >= 3 && l[0].IsSymbol("_") {
		switch l[1].Atom {
		case "to_fp":
			s := c.FPSort(atoi(l[2]), atoi(l[3]))
			if len(args) == 1 {
				// From the IEEE 754 bits.
				if args[0].Op == OpBVLit {
					return c.MkFPBits(args[0].Int.Uint64(), s), nil
				}
				return c.MkOther("to_fp", s, []int{s.EBits, s.SBits}, args...), nil
			}
			return c.MkFPToFP(args[0], args[1], s), nil
		case "to_fp_unsigned":
			s := c.FPSort(atoi(l[2]), atoi(l[3]))
			return c.MkFPToFPUnsigned(args[0], args[1], s), nil
		case "fp.to_sbv":
			return c.MkFPToBV(args[0], args[1], atoi(l[2]), true), nil
		case "fp.to_ubv":
			return c.MkFPToBV(args[0], args[1], atoi(l[2]), false), nil
		case "int2bv":
			return c.MkInt2BV(atoi(l[2]), args[0]), nil
		case "extract":
			return c.MkBVExtract(atoi(l[2]), atoi(l[3]), args[0]), nil
		case "zero_extend":
			return c.MkBVZeroExt(atoi(l[2]), args[0]), nil
		case "sign_extend":
			n := atoi(l[2])
			return c.intern(&Term{Op: OpSignExt, Sort: c.BVSort(args[0].Sort.Size + n), Idx: []int{n}, Args: args}), nil
		}
	}
	return nil, fmt.Errorf("unsupported %s", head)
}

var stringAliases = map[string]Op{
	"str.++": OpSeqConcat, "str.len": OpSeqLen, "str.contains": OpSeqContains,
	"str.prefixof": OpSeqPrefix, "str.suffixof": OpSeqSuffix, "str.indexof": OpSeqIndexOf,
	"str.last_indexof": OpSeqLastIndexOf, "str.substr": OpSeqExtract, "str.at": OpSeqAt,
	"str.replace": OpSeqReplace, "str.to.int": OpStrToInt, "int.to.str": OpStrFromInt,
	"str.to_int": OpStrToInt, "str.from_int": OpStrFromInt,
}

func (b *termBuilder) builtin(name string, args []*Term) (*Term, bool) {
	c := b.c
	if op, ok := stringAliases[name]; ok {
		name = string(op)
	}
	n := len(args)
	switch Op(name) {
	case OpNot:
		return c.MkNot(args[0]), true
	case OpAnd:
		return c.MkAnd(args...), true
	case OpOr:
		return c.MkOr(args...), true
	case OpImplies:
		return c.MkImplies(args[0], args[1]), true
	case OpXor:
		return c.MkXor(args[0], args[1]), true
	case OpEq:
		if n == 2 {
			return c.MkEq(args[0], args[1]), true
		}
		return c.mk(OpEq, c.boolSort, args...), true
	case OpDistinct:
		return c.MkDistinct(args...), true
	case OpITE:
		return c.MkITE(args[0], args[1], args[2]), true
	case OpAdd:
		return c.MkAdd(args...), true
	case OpSub:
		if n == 1 {
			if args[0].Op == OpIntLit {
				return c.MkIntBig(new(big.Int).Neg(args[0].Int)), true
			}
			return c.MkUnaryMinus(args[0]), true
		}
		return c.MkSub(args...), true
	case OpMul:
		return c.MkMul(args...), true
	case OpDiv:
		return c.MkDiv(args[0], args[1]), true
	case OpMod:
		return c.MkMod(args[0], args[1]), true
	case OpRem:
		return c.MkRem(args[0], args[1]), true
	case OpAbs:
		return c.mk(OpAbs, args[0].Sort, args[0]), true
	case OpLt:
		return c.MkLt(args[0], args[1]), true
	case OpLe:
		return c.MkLe(args[0], args[1]), true
	case OpGt:
		return c.MkGt(args[0], args[1]), true
	case OpGe:
		return c.MkGe(args[0], args[1]), true
	case OpToReal:
		return c.MkToReal(args[0]), true
	case OpToInt:
		return c.MkToInt(args[0]), true
	case OpIsInt:
		return c.MkIsInt(args[0]), true
	case OpSelect:
		return c.MkSelect(args[0], args[1]), true
	case OpStore:
		return c.MkStore(args[0], args[1], args[2]), true
	case OpSeqUnit:
		return c.MkUnit(args[0]), true
	case OpSeqConcat:
		return c.MkConcat(args...), true
	case OpSeqLen:
		return c.MkLength(args[0]), true
	case OpSeqNth:
		return c.MkNth(args[0], args[1]), true
	case OpSeqNthI:
		return c.MkSeqNthI(args[0], args[1]), true
	case OpSeqNthU:
		return c.MkSeqNthU(args[0], args[1]), true
	case OpSeqContains:
		return c.MkContains(args[0], args[1]), true
	case OpSeqPrefix:
		return c.MkPrefixOf(args[0], args[1]), true
	case OpSeqSuffix:
		return c.MkSuffixOf(args[0], args[1]), true
	case OpSeqIndexOf:
		if n == 2 {
			return c.mk(OpSeqIndexOf, c.intSort, args...), true
		}
		return c.MkIndexOf(args[0], args[1], args[2]), true
	case OpSeqLastIndexOf:
		return c.MkLastIndexOf(args[0], args[1]), true
	case OpSeqExtract:
		return c.MkExtract(args[0], args[1], args[2]), true
	case OpSeqAt:
		return c.MkAt(args[0], args[1]), true
	case OpSeqReplace:
		return c.MkReplace(args[0], args[1], args[2]), true
	case OpStrLt:
		return c.MkStringLt(args[0], args[1]), true
	case OpStrLe:
		return c.MkStringLe(args[0], args[1]), true
	case OpStrToInt:
		return c.MkStrToInt(args[0]), true
	case OpStrFromInt:
		return c.MkIntToStr(args[0]), true
	case OpStrLower:
		return c.MkStrLower(args[0]), true
	case OpStrUpper:
		return c.MkStrUpper(args[0]), true
	case OpFPIsNaN, OpFPIsZero, OpFPIsNeg, OpFPIsPos, OpFPIsInf, OpFPIsNormal, OpFPIsSubnormal,
		OpFPLt, OpFPLe, OpFPGt, OpFPGe, OpFPEq:
		return c.fpPred(Op(name), args...), true
	case OpFPAbs, OpFPNeg:
		return c.mk(Op(name), args[0].Sort, args[0]), true
	case OpFPAdd, OpFPSub, OpFPMul, OpFPDiv:
		return c.mk(Op(name), args[1].Sort, args...), true
	case OpFPRem, OpFPMin, OpFPMax:
		return c.mk(Op(name), args[0].Sort, args...), true
	case OpFPSqrt, OpFPRoundToInt:
		return c.mk(Op(name), args[1].Sort, args...), true
	case OpFPToReal:
		return c.MkFPToReal(args[0]), true
	case OpFPToIEEEBV:
		return c.MkFPToIEEEBV(args[0]), true
	case OpFPFromBits:
		s := c.FPSort(args[1].Sort.Size, args[2].Sort.Size+1)
		if args[0].Op == OpBVLit && args[1].Op == OpBVLit && args[2].Op == OpBVLit {
			bits := args[0].Int.Uint64()<<(s.EBits+s.SBits-1) | args[1].Int.Uint64()<<(s.SBits-1) | args[2].Int.Uint64()
			return c.MkFPBits(bits, s), true
		}
		return c.mk(OpFPFromBits, s, args...), true
	case OpUBV2Int, OpBV2Int:
		return c.MkUBV2Int(args[0]), true
	case OpBVSlt, OpBVSle, OpBVUlt, OpBVUle:
		return c.mk(Op(name), c.boolSort, args...), true
	case OpBVAdd, OpBVSub, OpBVMul, OpBVAnd, OpBVOr, OpBVXor, OpBVShl, OpBVLshr:
		return c.mk(Op(name), args[0].Sort, args...), true
	case OpBVNot, OpBVNeg:
		return c.mk(Op(name), args[0].Sort, args...), true
	case OpConcatBV:
		return c.mk(OpConcatBV, c.BVSort(args[0].Sort.Size+args[1].Sort.Size), args...), true
	}
	return nil, false
}
