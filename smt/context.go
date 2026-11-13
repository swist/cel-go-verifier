package smt

import (
	"fmt"
	"math"
	"math/big"
	"strconv"
	"strings"
	"sync"
)

// Context creates and interns sorts, declarations and terms. It mirrors
// com.microsoft.z3.Context: the mk* methods build terms without simplifying
// them. A Context is not safe for concurrent use.
type Context struct {
	mu     sync.Mutex
	sorts  map[string]*Sort
	decls  map[string]*FuncDecl
	terms  map[string]*Term
	nextID uint64
	fresh  int

	// declOrder lists the uninterpreted declarations in creation order.
	declOrder []*FuncDecl
	// sortOrder lists the uninterpreted and datatype sorts in creation order.
	sortOrder  []*Sort
	declByName map[string][]*FuncDecl
	sortByName map[string]*Sort

	backend Backend

	boolSort, intSort, realSort, stringSort, rmSort *Sort
	trueT, falseT                                   *Term
}

// NewContext returns a new context whose simplification is delegated to backend.
func NewContext(backend Backend) *Context {
	c := &Context{
		sorts:      map[string]*Sort{},
		decls:      map[string]*FuncDecl{},
		terms:      map[string]*Term{},
		declByName: map[string][]*FuncDecl{},
		sortByName: map[string]*Sort{},
		backend:    backend,
	}
	c.boolSort = c.internSort(&Sort{Kind: KindBool, key: "Bool"})
	c.intSort = c.internSort(&Sort{Kind: KindInt, key: "Int"})
	c.realSort = c.internSort(&Sort{Kind: KindReal, key: "Real"})
	c.stringSort = c.internSort(&Sort{Kind: KindString, key: "String"})
	c.rmSort = c.internSort(&Sort{Kind: KindRoundingMode, key: "RoundingMode"})
	c.trueT = c.intern(&Term{Op: OpTrue, Sort: c.boolSort})
	c.falseT = c.intern(&Term{Op: OpFalse, Sort: c.boolSort})
	return c
}

// Backend returns the backend of the context.
func (c *Context) Backend() Backend { return c.backend }

// ---------------------------------------------------------------------------
// Sorts

func (c *Context) internSort(s *Sort) *Sort {
	if e, ok := c.sorts[s.key]; ok {
		return e
	}
	c.sorts[s.key] = s
	return s
}

// BoolSort returns the Boolean sort.
func (c *Context) BoolSort() *Sort { return c.boolSort }

// IntSort returns the integer sort.
func (c *Context) IntSort() *Sort { return c.intSort }

// RealSort returns the real sort.
func (c *Context) RealSort() *Sort { return c.realSort }

// StringSort returns the string sort.
func (c *Context) StringSort() *Sort { return c.stringSort }

// RoundingModeSort returns the rounding mode sort.
func (c *Context) RoundingModeSort() *Sort { return c.rmSort }

// CharSort returns the character sort.
func (c *Context) CharSort() *Sort { return c.internSort(&Sort{Kind: KindChar, key: "Unicode"}) }

// SeqSort returns the sequence sort over elem.
func (c *Context) SeqSort(elem *Sort) *Sort {
	if elem.Kind == KindChar {
		return c.stringSort
	}
	return c.internSort(&Sort{Kind: KindSeq, Params: []*Sort{elem}, key: "Seq(" + elem.key + ")"})
}

// ArraySort returns the array sort from domain to rng.
func (c *Context) ArraySort(domain, rng *Sort) *Sort {
	return c.internSort(&Sort{Kind: KindArray, Params: []*Sort{domain, rng}, key: "Array(" + domain.key + "," + rng.key + ")"})
}

// FPSort returns the floating point sort with the given exponent and significand bits.
func (c *Context) FPSort(ebits, sbits int) *Sort {
	return c.internSort(&Sort{Kind: KindFP, EBits: ebits, SBits: sbits, key: fmt.Sprintf("FP(%d,%d)", ebits, sbits)})
}

// FPSortDouble returns the IEEE 754 double sort.
func (c *Context) FPSortDouble() *Sort { return c.FPSort(11, 53) }

// FPSortSingle returns the IEEE 754 single sort.
func (c *Context) FPSortSingle() *Sort { return c.FPSort(8, 24) }

// BVSort returns the bit-vector sort of the given size.
func (c *Context) BVSort(size int) *Sort {
	return c.internSort(&Sort{Kind: KindBV, Size: size, key: fmt.Sprintf("BV(%d)", size)})
}

// MkUninterpretedSort returns the uninterpreted sort with the given name.
func (c *Context) MkUninterpretedSort(name string) *Sort {
	key := "U:" + name
	if s, ok := c.sorts[key]; ok {
		return s
	}
	s := c.internSort(&Sort{Kind: KindUninterpreted, Name: name, key: key})
	c.sortOrder = append(c.sortOrder, s)
	c.sortByName[name] = s
	return s
}

// MkDatatypeSort creates a datatype sort. Field sorts that are nil refer to the datatype itself.
func (c *Context) MkDatatypeSort(name string, cons []ConstructorSpec) *Sort {
	key := "D:" + name
	if s, ok := c.sorts[key]; ok {
		return s
	}
	dt := &Datatype{Name: name}
	s := c.internSort(&Sort{Kind: KindDatatype, Name: name, Datatype: dt, key: key})
	for _, spec := range cons {
		k := &Constructor{Name: spec.Name, TesterName: spec.TesterName, FieldNames: spec.FieldNames}
		for _, fs := range spec.FieldSorts {
			if fs == nil {
				fs = s
			}
			k.FieldSorts = append(k.FieldSorts, fs)
		}
		k.Decl = c.internDecl(&FuncDecl{Name: spec.Name, Domain: k.FieldSorts, Range: s, Kind: DeclConstructor, Cons: k})
		k.Tester = c.internDecl(&FuncDecl{Name: spec.TesterName, Domain: []*Sort{s}, Range: c.boolSort, Kind: DeclTester, Cons: k})
		for i, fn := range spec.FieldNames {
			k.Accessors = append(k.Accessors, c.internDecl(&FuncDecl{Name: fn, Domain: []*Sort{s}, Range: k.FieldSorts[i], Kind: DeclAccessor, Cons: k, Field: i}))
		}
		dt.Constructors = append(dt.Constructors, k)
	}
	c.sortOrder = append(c.sortOrder, s)
	c.sortByName[name] = s
	return s
}

// Sorts returns the uninterpreted and datatype sorts in creation order.
func (c *Context) Sorts() []*Sort { return append([]*Sort(nil), c.sortOrder...) }

// SortByName looks up an uninterpreted or datatype sort.
func (c *Context) SortByName(name string) *Sort { return c.sortByName[name] }

// ---------------------------------------------------------------------------
// Declarations

func (c *Context) internDecl(d *FuncDecl) *FuncDecl {
	d.key = fmt.Sprintf("%d:%s(%s)%s", d.Kind, d.Name, sortListKey(d.Domain), d.Range.key)
	if e, ok := c.decls[d.key]; ok {
		return e
	}
	c.decls[d.key] = d
	c.declByName[d.Name] = append(c.declByName[d.Name], d)
	if d.Kind == DeclUninterpreted {
		c.declOrder = append(c.declOrder, d)
	}
	return d
}

// MkFuncDecl returns the uninterpreted function with the given name and signature.
func (c *Context) MkFuncDecl(name string, domain []*Sort, rng *Sort) *FuncDecl {
	return c.internDecl(&FuncDecl{Name: name, Domain: append([]*Sort(nil), domain...), Range: rng})
}

// Decls returns the uninterpreted declarations in creation order.
func (c *Context) Decls() []*FuncDecl { return append([]*FuncDecl(nil), c.declOrder...) }

// DeclsByName returns the declarations with the given name.
func (c *Context) DeclsByName(name string) []*FuncDecl { return c.declByName[name] }

// ---------------------------------------------------------------------------
// Terms

func (c *Context) intern(t *Term) *Term {
	var sb strings.Builder
	sb.WriteString(string(t.Op))
	sb.WriteByte('|')
	if t.Decl != nil {
		sb.WriteString(t.Decl.key)
	}
	sb.WriteByte('|')
	sb.WriteString(t.Sort.key)
	for _, i := range t.Idx {
		sb.WriteString("|i")
		sb.WriteString(strconv.Itoa(i))
	}
	switch t.Op {
	case OpIntLit, OpBVLit:
		sb.WriteString("|n")
		sb.WriteString(t.Int.String())
	case OpStrLit:
		sb.WriteString("|s")
		for _, r := range t.Runes {
			sb.WriteString(strconv.Itoa(int(r)))
			sb.WriteByte(',')
		}
	case OpFPLit:
		sb.WriteString("|f")
		sb.WriteString(strconv.FormatUint(t.Bits, 16))
	case OpRM:
		sb.WriteString("|r")
		sb.WriteString(strconv.Itoa(int(t.RM)))
	case OpCharLit:
		sb.WriteString("|c")
		sb.WriteString(t.Int.String())
	}
	if t.Name != "" {
		sb.WriteString("|N")
		sb.WriteString(t.Name)
	}
	for _, v := range t.Vars {
		sb.WriteString("|v")
		sb.WriteString(strconv.FormatUint(v.id, 10))
	}
	for _, a := range t.Args {
		sb.WriteString("|a")
		sb.WriteString(strconv.FormatUint(a.id, 10))
	}
	key := sb.String()
	if e, ok := c.terms[key]; ok {
		return e
	}
	c.nextID++
	t.id = c.nextID
	t.key = key
	c.terms[key] = t
	return t
}

func (c *Context) mk(op Op, sort *Sort, args ...*Term) *Term {
	return c.intern(&Term{Op: op, Sort: sort, Args: args})
}

// MkTrue returns true.
func (c *Context) MkTrue() *Term { return c.trueT }

// MkFalse returns false.
func (c *Context) MkFalse() *Term { return c.falseT }

// MkBool returns the Boolean literal b.
func (c *Context) MkBool(b bool) *Term {
	if b {
		return c.trueT
	}
	return c.falseT
}

// MkConst returns the constant with the given name and sort.
func (c *Context) MkConst(name string, sort *Sort) *Term {
	return c.MkApp(c.MkFuncDecl(name, nil, sort))
}

// MkBoolConst returns the Boolean constant with the given name.
func (c *Context) MkBoolConst(name string) *Term { return c.MkConst(name, c.boolSort) }

// MkFreshConst returns a new constant named prefix!N, as Z3 does.
func (c *Context) MkFreshConst(prefix string, sort *Sort) *Term {
	name := fmt.Sprintf("%s!%d", prefix, c.fresh)
	c.fresh++
	return c.MkConst(name, sort)
}

// MkApp applies decl to args.
func (c *Context) MkApp(decl *FuncDecl, args ...*Term) *Term {
	if len(args) != len(decl.Domain) {
		panic(fmt.Sprintf("smt: %s expects %d arguments, got %d", decl.Name, len(decl.Domain), len(args)))
	}
	for i, a := range args {
		if a.Sort != decl.Domain[i] {
			panic(fmt.Sprintf("smt: argument %d of %s has sort %s, want %s", i, decl.Name, a.Sort, decl.Domain[i]))
		}
	}
	return c.intern(&Term{Op: OpApp, Decl: decl, Sort: decl.Range, Args: append([]*Term(nil), args...)})
}

func (c *Context) checkBool(op Op, args ...*Term) {
	for _, a := range args {
		if a.Sort != c.boolSort {
			panic(fmt.Sprintf("smt: %s expects Bool arguments, got %s", op, a.Sort))
		}
	}
}

// MkNot returns (not a).
func (c *Context) MkNot(a *Term) *Term {
	c.checkBool(OpNot, a)
	return c.mk(OpNot, c.boolSort, a)
}

// MkAnd returns (and args...). Like Z3, a single argument still yields (and a).
func (c *Context) MkAnd(args ...*Term) *Term {
	c.checkBool(OpAnd, args...)
	if len(args) == 0 {
		return c.trueT
	}
	return c.mk(OpAnd, c.boolSort, append([]*Term(nil), args...)...)
}

// MkOr returns (or args...).
func (c *Context) MkOr(args ...*Term) *Term {
	c.checkBool(OpOr, args...)
	if len(args) == 0 {
		return c.falseT
	}
	return c.mk(OpOr, c.boolSort, append([]*Term(nil), args...)...)
}

// MkImplies returns (=> a b).
func (c *Context) MkImplies(a, b *Term) *Term {
	c.checkBool(OpImplies, a, b)
	return c.mk(OpImplies, c.boolSort, a, b)
}

// MkXor returns (xor a b).
func (c *Context) MkXor(a, b *Term) *Term {
	c.checkBool(OpXor, a, b)
	return c.mk(OpXor, c.boolSort, a, b)
}

// MkEq returns (= a b).
func (c *Context) MkEq(a, b *Term) *Term {
	if a.Sort != b.Sort {
		panic(fmt.Sprintf("smt: = of %s and %s", a.Sort, b.Sort))
	}
	return c.mk(OpEq, c.boolSort, a, b)
}

// MkDistinct returns (distinct args...).
func (c *Context) MkDistinct(args ...*Term) *Term {
	return c.mk(OpDistinct, c.boolSort, append([]*Term(nil), args...)...)
}

// MkITE returns (ite cond a b).
func (c *Context) MkITE(cond, a, b *Term) *Term {
	c.checkBool(OpITE, cond)
	if a.Sort != b.Sort {
		panic(fmt.Sprintf("smt: ite branches of %s and %s", a.Sort, b.Sort))
	}
	return c.mk(OpITE, a.Sort, cond, a, b)
}

// ---------------------------------------------------------------------------
// Arithmetic

// MkInt returns the integer numeral v.
func (c *Context) MkInt(v int64) *Term { return c.MkIntBig(big.NewInt(v)) }

// MkIntString returns the integer numeral written in decimal in s.
func (c *Context) MkIntString(s string) *Term {
	v, ok := new(big.Int).SetString(s, 10)
	if !ok {
		panic("smt: bad integer numeral " + s)
	}
	return c.MkIntBig(v)
}

// MkIntBig returns the integer numeral v.
func (c *Context) MkIntBig(v *big.Int) *Term {
	return c.intern(&Term{Op: OpIntLit, Sort: c.intSort, Int: new(big.Int).Set(v)})
}

// MkRealBig returns the real numeral num/den.
func (c *Context) MkReal(v *big.Rat) *Term {
	// Reals are printed as decimals or (/ n d); stored as a two element Idx free literal.
	return c.intern(&Term{Op: OpOther, Name: "#real:" + v.RatString(), Sort: c.realSort})
}

func (c *Context) arith(op Op, args ...*Term) *Term {
	sort := args[0].Sort
	for _, a := range args {
		if a.Sort.Kind != KindInt && a.Sort.Kind != KindReal {
			panic(fmt.Sprintf("smt: %s expects arithmetic arguments, got %s", op, a.Sort))
		}
		if a.Sort.Kind == KindReal {
			sort = c.realSort
		}
	}
	return c.mk(op, sort, append([]*Term(nil), args...)...)
}

// MkAdd returns (+ args...).
func (c *Context) MkAdd(args ...*Term) *Term { return c.arith(OpAdd, args...) }

// MkSub returns (- args...).
func (c *Context) MkSub(args ...*Term) *Term { return c.arith(OpSub, args...) }

// MkMul returns (* args...).
func (c *Context) MkMul(args ...*Term) *Term { return c.arith(OpMul, args...) }

// MkDiv returns (div a b) for integers, or (/ a b) for reals.
func (c *Context) MkDiv(a, b *Term) *Term {
	if a.Sort.Kind == KindReal || b.Sort.Kind == KindReal {
		return c.intern(&Term{Op: OpOther, Name: "/", Sort: c.realSort, Args: []*Term{a, b}})
	}
	return c.arith(OpDiv, a, b)
}

// MkMod returns (mod a b).
func (c *Context) MkMod(a, b *Term) *Term { return c.arith(OpMod, a, b) }

// MkRem returns (rem a b).
func (c *Context) MkRem(a, b *Term) *Term { return c.arith(OpRem, a, b) }

// MkUnaryMinus returns (- a).
func (c *Context) MkUnaryMinus(a *Term) *Term { return c.arith(OpNeg, a) }

// MkLt returns (< a b).
func (c *Context) MkLt(a, b *Term) *Term { c.arith(OpLt, a, b); return c.mk(OpLt, c.boolSort, a, b) }

// MkLe returns (<= a b).
func (c *Context) MkLe(a, b *Term) *Term { c.arith(OpLe, a, b); return c.mk(OpLe, c.boolSort, a, b) }

// MkGt returns (> a b).
func (c *Context) MkGt(a, b *Term) *Term { c.arith(OpGt, a, b); return c.mk(OpGt, c.boolSort, a, b) }

// MkGe returns (>= a b).
func (c *Context) MkGe(a, b *Term) *Term { c.arith(OpGe, a, b); return c.mk(OpGe, c.boolSort, a, b) }

// MkToReal returns (to_real a).
func (c *Context) MkToReal(a *Term) *Term { return c.mk(OpToReal, c.realSort, a) }

// MkToInt returns (to_int a).
func (c *Context) MkToInt(a *Term) *Term { return c.mk(OpToInt, c.intSort, a) }

// MkIsInt returns (is_int a).
func (c *Context) MkIsInt(a *Term) *Term { return c.mk(OpIsInt, c.boolSort, a) }

// ---------------------------------------------------------------------------
// Arrays

// MkSelect returns (select a i).
func (c *Context) MkSelect(a, i *Term) *Term {
	if a.Sort.Kind != KindArray || a.Sort.Domain() != i.Sort {
		panic(fmt.Sprintf("smt: select from %s at %s", a.Sort, i.Sort))
	}
	return c.mk(OpSelect, a.Sort.Range(), a, i)
}

// MkStore returns (store a i v).
func (c *Context) MkStore(a, i, v *Term) *Term {
	if a.Sort.Kind != KindArray || a.Sort.Domain() != i.Sort || a.Sort.Range() != v.Sort {
		panic(fmt.Sprintf("smt: store into %s at %s of %s", a.Sort, i.Sort, v.Sort))
	}
	return c.mk(OpStore, a.Sort, a, i, v)
}

// MkConstArray returns ((as const (Array domain (sort v))) v).
func (c *Context) MkConstArray(domain *Sort, v *Term) *Term {
	return c.mk(OpConstArray, c.ArraySort(domain, v.Sort), v)
}

// ---------------------------------------------------------------------------
// Sequences and strings

// MkString returns the string literal s.
func (c *Context) MkString(s string) *Term { return c.MkStringRunes([]rune(s)) }

// MkStringRunes returns the string literal with the given code points.
func (c *Context) MkStringRunes(r []rune) *Term {
	return c.intern(&Term{Op: OpStrLit, Sort: c.stringSort, Runes: append([]rune{}, r...)})
}

// MkEmptySeq returns the empty sequence of the given sort.
func (c *Context) MkEmptySeq(sort *Sort) *Term {
	if sort.Kind == KindString {
		return c.MkString("")
	}
	return c.intern(&Term{Op: OpSeqEmpty, Sort: sort})
}

// MkUnit returns (seq.unit e).
func (c *Context) MkUnit(e *Term) *Term { return c.mk(OpSeqUnit, c.SeqSort(e.Sort), e) }

// MkConcat returns (seq.++ args...).
func (c *Context) MkConcat(args ...*Term) *Term {
	for _, a := range args[1:] {
		if a.Sort != args[0].Sort {
			panic(fmt.Sprintf("smt: concat of %s and %s", args[0].Sort, a.Sort))
		}
	}
	return c.mk(OpSeqConcat, args[0].Sort, append([]*Term(nil), args...)...)
}

// MkLength returns (seq.len s).
func (c *Context) MkLength(s *Term) *Term { c.seq(s); return c.mk(OpSeqLen, c.intSort, s) }

// MkNth returns (seq.nth s i).
func (c *Context) MkNth(s, i *Term) *Term {
	c.seq(s)
	elem := c.CharSort()
	if s.Sort.Kind == KindSeq {
		elem = s.Sort.Elem()
	}
	return c.mk(OpSeqNth, elem, s, i)
}

// MkAt returns (seq.at s i).
func (c *Context) MkAt(s, i *Term) *Term { c.seq(s); return c.mk(OpSeqAt, s.Sort, s, i) }

// MkContains returns (seq.contains s sub).
func (c *Context) MkContains(s, sub *Term) *Term {
	c.seq(s)
	return c.mk(OpSeqContains, c.boolSort, s, sub)
}

// MkPrefixOf returns (seq.prefixof pre s).
func (c *Context) MkPrefixOf(pre, s *Term) *Term { return c.mk(OpSeqPrefix, c.boolSort, pre, s) }

// MkSuffixOf returns (seq.suffixof suf s).
func (c *Context) MkSuffixOf(suf, s *Term) *Term { return c.mk(OpSeqSuffix, c.boolSort, suf, s) }

// MkIndexOf returns (seq.indexof s sub offset).
func (c *Context) MkIndexOf(s, sub, offset *Term) *Term {
	return c.mk(OpSeqIndexOf, c.intSort, s, sub, offset)
}

// MkLastIndexOf returns (seq.last_indexof s sub).
func (c *Context) MkLastIndexOf(s, sub *Term) *Term {
	return c.mk(OpSeqLastIndexOf, c.intSort, s, sub)
}

// MkExtract returns (seq.extract s offset length).
func (c *Context) MkExtract(s, offset, length *Term) *Term {
	return c.mk(OpSeqExtract, s.Sort, s, offset, length)
}

// MkReplace returns (seq.replace s src dst).
func (c *Context) MkReplace(s, src, dst *Term) *Term {
	return c.mk(OpSeqReplace, s.Sort, s, src, dst)
}

// MkStringLt returns (str.< a b).
func (c *Context) MkStringLt(a, b *Term) *Term { return c.mk(OpStrLt, c.boolSort, a, b) }

// MkStringLe returns (str.<= a b).
func (c *Context) MkStringLe(a, b *Term) *Term { return c.mk(OpStrLe, c.boolSort, a, b) }

// MkStrToInt returns (str.to_int s).
func (c *Context) MkStrToInt(s *Term) *Term { return c.mk(OpStrToInt, c.intSort, s) }

// MkIntToStr returns (str.from_int i).
func (c *Context) MkIntToStr(i *Term) *Term { return c.mk(OpStrFromInt, c.stringSort, i) }

// MkStrLower returns (str.lower s).
func (c *Context) MkStrLower(s *Term) *Term { return c.mk(OpStrLower, c.stringSort, s) }

// MkStrUpper returns (str.upper s).
func (c *Context) MkStrUpper(s *Term) *Term { return c.mk(OpStrUpper, c.stringSort, s) }

func (c *Context) seq(s *Term) {
	if !s.Sort.IsSeqLike() {
		panic(fmt.Sprintf("smt: expected a sequence, got %s", s.Sort))
	}
}

// ---------------------------------------------------------------------------
// Floating point

// MkFP returns the floating point literal v in the given sort (rounded to nearest, ties to even).
func (c *Context) MkFP(v float64, sort *Sort) *Term {
	var bits uint64
	switch {
	case sort.EBits == 11 && sort.SBits == 53:
		bits = math.Float64bits(v)
		if math.IsNaN(v) {
			bits = 0x7ff8000000000000
		}
	case sort.EBits == 8 && sort.SBits == 24:
		f := float32(v)
		bits = uint64(math.Float32bits(f))
		if math.IsNaN(v) {
			bits = 0x7fc00000
		}
	default:
		panic("smt: unsupported floating point sort " + sort.String())
	}
	return c.MkFPBits(bits, sort)
}

// MkFPBits returns the floating point literal with the given IEEE 754 encoding.
func (c *Context) MkFPBits(bits uint64, sort *Sort) *Term {
	eb, sb := uint(sort.EBits), uint(sort.SBits)
	expMask := uint64(1)<<eb - 1
	sigMask := uint64(1)<<(sb-1) - 1
	if (bits>>(sb-1))&expMask == expMask && bits&sigMask != 0 {
		// Canonical NaN.
		bits = expMask<<(sb-1) | uint64(1)<<(sb-2)
	}
	return c.intern(&Term{Op: OpFPLit, Sort: sort, Bits: bits})
}

// MkFPNaN returns NaN of the given sort.
func (c *Context) MkFPNaN(sort *Sort) *Term { return c.MkFP(math.NaN(), sort) }

// MkFPRoundingMode returns a rounding mode literal.
func (c *Context) MkFPRoundingMode(rm RoundingMode) *Term {
	return c.intern(&Term{Op: OpRM, Sort: c.rmSort, RM: rm})
}

// MkFPRoundNearestTiesToEven returns RNE.
func (c *Context) MkFPRoundNearestTiesToEven() *Term { return c.MkFPRoundingMode(RNE) }

// MkFPRoundTowardZero returns RTZ.
func (c *Context) MkFPRoundTowardZero() *Term { return c.MkFPRoundingMode(RTZ) }

func (c *Context) fpPred(op Op, args ...*Term) *Term { return c.mk(op, c.boolSort, args...) }

// MkFPIsNaN returns (fp.isNaN a).
func (c *Context) MkFPIsNaN(a *Term) *Term { return c.fpPred(OpFPIsNaN, a) }

// MkFPIsZero returns (fp.isZero a).
func (c *Context) MkFPIsZero(a *Term) *Term { return c.fpPred(OpFPIsZero, a) }

// MkFPIsNegative returns (fp.isNegative a).
func (c *Context) MkFPIsNegative(a *Term) *Term { return c.fpPred(OpFPIsNeg, a) }

// MkFPIsPositive returns (fp.isPositive a).
func (c *Context) MkFPIsPositive(a *Term) *Term { return c.fpPred(OpFPIsPos, a) }

// MkFPIsInfinite returns (fp.isInfinite a).
func (c *Context) MkFPIsInfinite(a *Term) *Term { return c.fpPred(OpFPIsInf, a) }

// MkFPLt returns (fp.lt a b).
func (c *Context) MkFPLt(a, b *Term) *Term { return c.fpPred(OpFPLt, a, b) }

// MkFPLEq returns (fp.leq a b).
func (c *Context) MkFPLEq(a, b *Term) *Term { return c.fpPred(OpFPLe, a, b) }

// MkFPGt returns (fp.gt a b).
func (c *Context) MkFPGt(a, b *Term) *Term { return c.fpPred(OpFPGt, a, b) }

// MkFPGEq returns (fp.geq a b).
func (c *Context) MkFPGEq(a, b *Term) *Term { return c.fpPred(OpFPGe, a, b) }

// MkFPEq returns (fp.eq a b).
func (c *Context) MkFPEq(a, b *Term) *Term { return c.fpPred(OpFPEq, a, b) }

// MkFPAbs returns (fp.abs a).
func (c *Context) MkFPAbs(a *Term) *Term { return c.mk(OpFPAbs, a.Sort, a) }

// MkFPNeg returns (fp.neg a).
func (c *Context) MkFPNeg(a *Term) *Term { return c.mk(OpFPNeg, a.Sort, a) }

// MkFPAdd returns (fp.add rm a b).
func (c *Context) MkFPAdd(rm, a, b *Term) *Term { return c.mk(OpFPAdd, a.Sort, rm, a, b) }

// MkFPSub returns (fp.sub rm a b).
func (c *Context) MkFPSub(rm, a, b *Term) *Term { return c.mk(OpFPSub, a.Sort, rm, a, b) }

// MkFPMul returns (fp.mul rm a b).
func (c *Context) MkFPMul(rm, a, b *Term) *Term { return c.mk(OpFPMul, a.Sort, rm, a, b) }

// MkFPDiv returns (fp.div rm a b).
func (c *Context) MkFPDiv(rm, a, b *Term) *Term { return c.mk(OpFPDiv, a.Sort, rm, a, b) }

// MkFPRem returns (fp.rem a b).
func (c *Context) MkFPRem(a, b *Term) *Term { return c.mk(OpFPRem, a.Sort, a, b) }

// MkFPRoundToIntegral returns (fp.roundToIntegral rm a).
func (c *Context) MkFPRoundToIntegral(rm, a *Term) *Term {
	return c.mk(OpFPRoundToInt, a.Sort, rm, a)
}

// MkFPToFP converts a floating point term to another floating point sort: ((_ to_fp e s) rm a).
func (c *Context) MkFPToFP(rm, a *Term, sort *Sort) *Term {
	return c.intern(&Term{Op: OpFPToFP, Sort: sort, Idx: []int{sort.EBits, sort.SBits}, Args: []*Term{rm, a}})
}

// MkFPToFPFromReal converts a real or integer term to floating point: ((_ to_fp e s) rm a).
func (c *Context) MkFPToFPFromReal(rm, a *Term, sort *Sort) *Term {
	return c.MkFPToFP(rm, a, sort)
}

// MkFPToFPSigned converts a signed bit-vector to floating point: ((_ to_fp e s) rm bv).
func (c *Context) MkFPToFPSigned(rm, bv *Term, sort *Sort) *Term { return c.MkFPToFP(rm, bv, sort) }

// MkFPToFPUnsigned converts an unsigned bit-vector to floating point.
func (c *Context) MkFPToFPUnsigned(rm, bv *Term, sort *Sort) *Term {
	return c.intern(&Term{Op: OpFPToFPUnsigned, Sort: sort, Idx: []int{sort.EBits, sort.SBits}, Args: []*Term{rm, bv}})
}

// MkFPToBV returns ((_ fp.to_sbv size) rm a) or ((_ fp.to_ubv size) rm a).
func (c *Context) MkFPToBV(rm, a *Term, size int, signed bool) *Term {
	op := OpFPToUBV
	if signed {
		op = OpFPToSBV
	}
	return c.intern(&Term{Op: op, Sort: c.BVSort(size), Idx: []int{size}, Args: []*Term{rm, a}})
}

// MkFPToReal returns (fp.to_real a).
func (c *Context) MkFPToReal(a *Term) *Term { return c.mk(OpFPToReal, c.realSort, a) }

// MkFPToIEEEBV returns (fp.to_ieee_bv a).
func (c *Context) MkFPToIEEEBV(a *Term) *Term {
	return c.mk(OpFPToIEEEBV, c.BVSort(a.Sort.EBits+a.Sort.SBits), a)
}

// ---------------------------------------------------------------------------
// Bit-vectors

// MkBV returns the bit-vector numeral v (taken modulo 2^size).
func (c *Context) MkBV(v *big.Int, size int) *Term {
	m := new(big.Int).Lsh(big.NewInt(1), uint(size))
	n := new(big.Int).Mod(v, m)
	return c.intern(&Term{Op: OpBVLit, Sort: c.BVSort(size), Int: n})
}

// MkBVSLT returns (bvslt a b).
func (c *Context) MkBVSLT(a, b *Term) *Term { return c.mk(OpBVSlt, c.boolSort, a, b) }

// MkBVULT returns (bvult a b).
func (c *Context) MkBVULT(a, b *Term) *Term { return c.mk(OpBVUlt, c.boolSort, a, b) }

// MkBVULE returns (bvule a b).
func (c *Context) MkBVULE(a, b *Term) *Term { return c.mk(OpBVUle, c.boolSort, a, b) }

// MkBVAnd returns (bvand a b).
func (c *Context) MkBVAnd(a, b *Term) *Term { return c.mk(OpBVAnd, a.Sort, a, b) }

// MkBVOr returns (bvor a b).
func (c *Context) MkBVOr(a, b *Term) *Term { return c.mk(OpBVOr, a.Sort, a, b) }

// MkBVNot returns (bvnot a).
func (c *Context) MkBVNot(a *Term) *Term { return c.mk(OpBVNot, a.Sort, a) }

// MkBVShl returns (bvshl a b).
func (c *Context) MkBVShl(a, b *Term) *Term { return c.mk(OpBVShl, a.Sort, a, b) }

// MkBVLshr returns (bvlshr a b).
func (c *Context) MkBVLshr(a, b *Term) *Term { return c.mk(OpBVLshr, a.Sort, a, b) }

// MkBVExtract returns ((_ extract hi lo) a).
func (c *Context) MkBVExtract(hi, lo int, a *Term) *Term {
	return c.intern(&Term{Op: OpExtract, Sort: c.BVSort(hi - lo + 1), Idx: []int{hi, lo}, Args: []*Term{a}})
}

// MkBVZeroExt returns ((_ zero_extend n) a).
func (c *Context) MkBVZeroExt(n int, a *Term) *Term {
	return c.intern(&Term{Op: OpZeroExt, Sort: c.BVSort(a.Sort.Size + n), Idx: []int{n}, Args: []*Term{a}})
}

// MkUBV2Int returns (ubv_to_int a).
func (c *Context) MkUBV2Int(a *Term) *Term { return c.mk(OpUBV2Int, c.intSort, a) }

// MkInt2BV returns ((_ int2bv size) a).
func (c *Context) MkInt2BV(size int, a *Term) *Term {
	return c.intern(&Term{Op: OpInt2BV, Sort: c.BVSort(size), Idx: []int{size}, Args: []*Term{a}})
}

// MkBV2Int converts a bit-vector to an integer as Z3_mk_bv2int does: unsigned
// is (ubv_to_int a); signed subtracts 2^size from negative values.
func (c *Context) MkBV2Int(a *Term, signed bool) *Term {
	r := c.MkUBV2Int(a)
	if !signed {
		return r
	}
	size := a.Sort.Size
	bound := new(big.Int).Lsh(big.NewInt(1), uint(size))
	return c.MkITE(c.MkBVSLT(a, c.MkBV(big.NewInt(0), size)), c.MkSub(r, c.MkIntBig(bound)), r)
}

// ---------------------------------------------------------------------------
// Other

// MkModelValue returns a model value (an element of an uninterpreted sort's universe).
func (c *Context) MkModelValue(name string, sort *Sort) *Term {
	return c.intern(&Term{Op: OpModelValue, Sort: sort, Name: name})
}

// MkOther builds an application of a builtin the term layer doesn't model.
func (c *Context) MkOther(name string, sort *Sort, idx []int, args ...*Term) *Term {
	return c.intern(&Term{Op: OpOther, Name: name, Sort: sort, Idx: idx, Args: append([]*Term(nil), args...)})
}

// MkBoundVar returns a variable bound by a binder.
func (c *Context) MkBoundVar(name string, sort *Sort) *Term {
	return c.intern(&Term{Op: OpVar, Name: name, Sort: sort})
}

// MkLambda returns (lambda (vars) body).
func (c *Context) MkLambda(vars []*Term, body *Term) *Term {
	var dom []*Sort
	for _, v := range vars {
		dom = append(dom, v.Sort)
	}
	if len(dom) != 1 {
		return c.intern(&Term{Op: OpLambda, Sort: c.ArraySort(dom[0], body.Sort), Vars: vars, Args: []*Term{body}})
	}
	return c.intern(&Term{Op: OpLambda, Sort: c.ArraySort(dom[0], body.Sort), Vars: vars, Args: []*Term{body}})
}

// MkAsArray returns (_ as-array f).
func (c *Context) MkAsArray(decl *FuncDecl) *Term {
	return c.intern(&Term{Op: OpAsArray, Decl: decl, Sort: c.ArraySort(decl.Domain[0], decl.Range)})
}

// MkQuantifier returns (forall (vars) body) or (exists (vars) body).
func (c *Context) MkQuantifier(universal bool, vars []*Term, body *Term) *Term {
	op := OpExists
	if universal {
		op = OpForall
	}
	return c.intern(&Term{Op: op, Sort: c.boolSort, Vars: vars, Args: []*Term{body}})
}

// MkSeqNthI returns (seq.nth_i s i), the interpreted part of seq.nth (as produced by simplification).
func (c *Context) MkSeqNthI(s, i *Term) *Term { return c.mk(OpSeqNthI, s.Sort.Elem(), s, i) }

// MkSeqNthU returns (seq.nth_u s i), the uninterpreted part of seq.nth.
func (c *Context) MkSeqNthU(s, i *Term) *Term { return c.mk(OpSeqNthU, s.Sort.Elem(), s, i) }

// Simplify simplifies t with the backend's simplifier.
func (c *Context) Simplify(t *Term) *Term {
	if t.Op == OpTrue || t.Op == OpFalse || t.Op == OpIntLit {
		return t
	}
	return c.backend.Simplify(c, t)
}

// Rebuild returns t with its arguments replaced by args.
func (c *Context) Rebuild(t *Term, args []*Term) *Term {
	same := len(args) == len(t.Args)
	for i := range args {
		if !same || args[i] != t.Args[i] {
			same = false
			break
		}
	}
	if same {
		return t
	}
	n := *t
	n.Args = append([]*Term(nil), args...)
	n.id = 0
	n.key = ""
	if n.Op == OpITE {
		n.Sort = args[1].Sort
	}
	return c.intern(&n)
}

// Substitute replaces every occurrence of from[i] in t with to[i], like Z3's Expr.substitute.
func (c *Context) Substitute(t *Term, from, to []*Term) *Term {
	m := make(map[*Term]*Term, len(from))
	for i := range from {
		m[from[i]] = to[i]
	}
	cache := map[*Term]*Term{}
	var walk func(*Term) *Term
	walk = func(t *Term) *Term {
		if r, ok := m[t]; ok {
			return r
		}
		if r, ok := cache[t]; ok {
			return r
		}
		args := make([]*Term, len(t.Args))
		for i, a := range t.Args {
			args[i] = walk(a)
		}
		r := c.Rebuild(t, args)
		cache[t] = r
		return r
	}
	return walk(t)
}
