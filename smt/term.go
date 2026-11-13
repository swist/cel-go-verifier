package smt

import (
	"math/big"
)

// Op identifies the operation of a term. Builtin operations are named after
// their SMT-LIB2 (or Z3) symbol; applications of declared functions use OpApp.
type Op string

// Operations.
const (
	OpTrue     Op = "true"
	OpFalse    Op = "false"
	OpNot      Op = "not"
	OpAnd      Op = "and"
	OpOr       Op = "or"
	OpImplies  Op = "=>"
	OpXor      Op = "xor"
	OpEq       Op = "="
	OpDistinct Op = "distinct"
	OpITE      Op = "ite"

	OpIntLit Op = "#int"
	OpStrLit Op = "#str"
	OpFPLit  Op = "#fp"
	OpBVLit  Op = "#bv"
	OpRM     Op = "#rm"

	OpAdd    Op = "+"
	OpSub    Op = "-"
	OpMul    Op = "*"
	OpDiv    Op = "div"
	OpMod    Op = "mod"
	OpRem    Op = "rem"
	OpNeg    Op = "#neg"
	OpLt     Op = "<"
	OpLe     Op = "<="
	OpGt     Op = ">"
	OpGe     Op = ">="
	OpAbs    Op = "abs"
	OpToInt  Op = "to_int"
	OpToReal Op = "to_real"
	OpIsInt  Op = "is_int"
	OpPower  Op = "^"

	OpApp Op = "#app"

	OpSelect     Op = "select"
	OpStore      Op = "store"
	OpConstArray Op = "#const"
	OpAsArray    Op = "#as-array"

	OpSeqEmpty       Op = "#seq.empty"
	OpSeqUnit        Op = "seq.unit"
	OpSeqConcat      Op = "seq.++"
	OpSeqLen         Op = "seq.len"
	OpSeqNth         Op = "seq.nth"
	OpSeqNthI        Op = "seq.nth_i"
	OpSeqNthU        Op = "seq.nth_u"
	OpSeqContains    Op = "seq.contains"
	OpSeqPrefix      Op = "seq.prefixof"
	OpSeqSuffix      Op = "seq.suffixof"
	OpSeqIndexOf     Op = "seq.indexof"
	OpSeqLastIndexOf Op = "seq.last_indexof"
	OpSeqExtract     Op = "seq.extract"
	OpSeqAt          Op = "seq.at"
	OpSeqReplace     Op = "seq.replace"
	OpStrLt          Op = "str.<"
	OpStrLe          Op = "str.<="
	OpStrToInt       Op = "str.to_int"
	OpStrFromInt     Op = "str.from_int"
	OpStrToCode      Op = "str.to_code"
	OpStrFromCode    Op = "str.from_code"
	OpStrInRe        Op = "str.in_re"
	OpStrToRe        Op = "str.to_re"
	OpStrLower       Op = "str.lower"
	OpStrUpper       Op = "str.upper"
	OpCharLit        Op = "#char"

	OpFPIsNaN        Op = "fp.isNaN"
	OpFPIsZero       Op = "fp.isZero"
	OpFPIsNeg        Op = "fp.isNegative"
	OpFPIsPos        Op = "fp.isPositive"
	OpFPIsInf        Op = "fp.isInfinite"
	OpFPIsNormal     Op = "fp.isNormal"
	OpFPIsSubnormal  Op = "fp.isSubnormal"
	OpFPAbs          Op = "fp.abs"
	OpFPNeg          Op = "fp.neg"
	OpFPAdd          Op = "fp.add"
	OpFPSub          Op = "fp.sub"
	OpFPMul          Op = "fp.mul"
	OpFPDiv          Op = "fp.div"
	OpFPRem          Op = "fp.rem"
	OpFPSqrt         Op = "fp.sqrt"
	OpFPMin          Op = "fp.min"
	OpFPMax          Op = "fp.max"
	OpFPLt           Op = "fp.lt"
	OpFPLe           Op = "fp.leq"
	OpFPGt           Op = "fp.gt"
	OpFPGe           Op = "fp.geq"
	OpFPEq           Op = "fp.eq"
	OpFPRoundToInt   Op = "fp.roundToIntegral"
	OpFPToFP         Op = "to_fp"
	OpFPToFPUnsigned Op = "to_fp_unsigned"
	OpFPToSBV        Op = "fp.to_sbv"
	OpFPToUBV        Op = "fp.to_ubv"
	OpFPToReal       Op = "fp.to_real"
	OpFPToIEEEBV     Op = "fp.to_ieee_bv"
	OpFPFromBits     Op = "fp"

	OpBV2Int   Op = "bv2int"
	OpUBV2Int  Op = "ubv_to_int"
	OpSBV2Int  Op = "sbv_to_int"
	OpInt2BV   Op = "int2bv"
	OpBVSlt    Op = "bvslt"
	OpBVSle    Op = "bvsle"
	OpBVUlt    Op = "bvult"
	OpBVUle    Op = "bvule"
	OpBVAdd    Op = "bvadd"
	OpBVSub    Op = "bvsub"
	OpBVMul    Op = "bvmul"
	OpBVAnd    Op = "bvand"
	OpBVOr     Op = "bvor"
	OpBVXor    Op = "bvxor"
	OpBVNot    Op = "bvnot"
	OpBVNeg    Op = "bvneg"
	OpBVShl    Op = "bvshl"
	OpBVLshr   Op = "bvlshr"
	OpExtract  Op = "extract"
	OpConcatBV Op = "concat"
	OpZeroExt  Op = "zero_extend"
	OpSignExt  Op = "sign_extend"

	OpModelValue Op = "#modelvalue"
	OpVar        Op = "#var"
	OpLambda     Op = "lambda"
	OpForall     Op = "forall"
	OpExists     Op = "exists"
	// OpOther is a builtin the term layer doesn't model; Name holds its symbol.
	OpOther Op = "#other"
)

// RoundingMode is an IEEE 754 rounding mode.
type RoundingMode int

// Rounding modes.
const (
	RNE RoundingMode = iota
	RNA
	RTP
	RTN
	RTZ
)

var rmNames = [...]string{"roundNearestTiesToEven", "roundNearestTiesToAway", "roundTowardPositive", "roundTowardNegative", "roundTowardZero"}

// Term is a hash-consed SMT term.
type Term struct {
	id   uint64
	Op   Op
	Decl *FuncDecl
	Args []*Term
	Sort *Sort
	// Idx holds the indices of an indexed operation, e.g. (_ to_fp 11 53).
	Idx []int
	// Int is the value of an integer or bit-vector literal.
	Int *big.Int
	// Runes is the value of a string literal, as code points.
	Runes []rune
	// Bits is the IEEE 754 encoding of a floating point literal. NaN is canonical.
	Bits uint64
	// RM is the rounding mode of a rounding mode literal.
	RM RoundingMode
	// Name is the symbol of a model value, bound variable or unmodelled builtin.
	Name string
	// Vars are the bound variables of a binder.
	Vars []*Term

	key string
}

// ID returns a unique identifier of the term within its context. IDs increase in creation order.
func (t *Term) ID() uint64 { return t.id }

// IsTrue reports whether t is the literal true.
func (t *Term) IsTrue() bool { return t.Op == OpTrue }

// IsFalse reports whether t is the literal false.
func (t *Term) IsFalse() bool { return t.Op == OpFalse }

// IsApp reports whether t is a function application in Z3's sense (anything but a binder or bound variable).
func (t *Term) IsApp() bool {
	return t.Op != OpLambda && t.Op != OpForall && t.Op != OpExists && t.Op != OpVar
}

// IsAppOf reports whether t applies decl.
func (t *Term) IsAppOf(decl *FuncDecl) bool { return t.Op == OpApp && t.Decl == decl }

// IsIntLit reports whether t is an integer numeral.
func (t *Term) IsIntLit() bool { return t.Op == OpIntLit }

// String prints t in SMT-LIB2 syntax.
func (t *Term) String() string { return Print(t) }

// DeclName returns the name of the applied declaration, or the builtin symbol.
func (t *Term) DeclName() string {
	switch t.Op {
	case OpApp:
		return t.Decl.Name
	case OpOther, OpModelValue:
		return t.Name
	default:
		return string(t.Op)
	}
}

// StringValue returns the value of a string literal.
func (t *Term) StringValue() string { return string(t.Runes) }
