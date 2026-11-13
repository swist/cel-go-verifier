package verifier

import (
	"fmt"
	"math"
	"math/big"
	"strconv"

	"github.com/swist/cel-go-verifier/smt"
)

// NanosPerSecond is the number of nanoseconds per second.
const NanosPerSecond = 1_000_000_000

const (
	timestampSecondsMin = -62135596800
	timestampSecondsMax = 253402300799
	durationSecondsMin  = -315576000000
	durationSecondsMax  = 315576000000
	maxNanos            = 999999999

	// MinInt64 is the smallest int64, in decimal.
	MinInt64 = "-9223372036854775808"
	// MaxInt64 is the largest int64, in decimal.
	MaxInt64 = "9223372036854775807"
	// MaxUint64 is the largest uint64, in decimal.
	MaxUint64 = "18446744073709551615"
)

var (
	twoTo63 = math.Ldexp(1, 63)
	twoTo64 = math.Ldexp(1, 64)

	minTimestampNanos     = totalNanos(timestampSecondsMin, 0)
	maxTimestampNanos     = totalNanos(timestampSecondsMax, maxNanos)
	minTotalDurationNanos = totalNanos(durationSecondsMin, -maxNanos)
	maxTotalDurationNanos = totalNanos(durationSecondsMax, maxNanos)
)

func totalNanos(seconds, nanos int64) string {
	v := new(big.Int).Mul(big.NewInt(seconds), big.NewInt(NanosPerSecond))
	return v.Add(v, big.NewInt(nanos)).String()
}

// Datatype names, as in the Java verifier.
const (
	genericUnknownID = "!generic_unknown"
)

// TypeSystem maps CEL values to Z3 terms: a CelValue datatype with one
// constructor per kind of value, and uninterpreted references to the contents
// of lists, maps, messages and optionals.
//
// A TypeSystem is bound to one smt.Context and one verification run; it must
// not be shared or reused. Axioms must only use the instance they're given.
type TypeSystem struct {
	c *smt.Context

	celValueSort *smt.Sort
	boolCons, intCons, uintCons, doubleCons, stringCons, bytesCons,
	timestampCons, durationCons, errorCons, unknownCons, nullCons,
	optionalCons, listCons, mapCons, messageCons *smt.Constructor

	unknownIDSort, optionalRefSort, listRefSort, mapRefSort, messageRefSort *smt.Sort

	optionalValueFunc, optionalOfRefFunc, asSeqFunc                *smt.FuncDecl
	mapValuesFunc, mapKeysFunc, mapPresenceFunc                    *smt.FuncDecl
	msgValuesFunc, msgPresenceFunc, msgTypeNameFunc                *smt.FuncDecl
	hasTruncatedTypeConstraintFunc, truncateDoubleFunc, hasFractionFunc *smt.FuncDecl

	// Doubles whose truncation and fraction are still uninterpreted, in order of first use.
	undefinedDoubles     []*smt.Term
	undefinedDoublesSeen map[*smt.Term]bool

	parameterizeUnknowns bool
}

// NewTypeSystem declares the CEL value encoding in c.
func NewTypeSystem(c *smt.Context, parameterizeUnknowns bool) *TypeSystem {
	ts := &TypeSystem{c: c, parameterizeUnknowns: parameterizeUnknowns, undefinedDoublesSeen: map[*smt.Term]bool{}}
	fp := c.FPSortDouble()
	ts.unknownIDSort = c.MkUninterpretedSort("UnknownId")
	ts.optionalRefSort = c.MkUninterpretedSort("OptionalRef")
	ts.listRefSort = c.MkUninterpretedSort("ListRef")
	ts.mapRefSort = c.MkUninterpretedSort("MapRef")
	ts.messageRefSort = c.MkUninterpretedSort("MessageRef")
	field := func(name, tester, getter string, s *smt.Sort) smt.ConstructorSpec {
		return smt.ConstructorSpec{Name: name, TesterName: tester, FieldNames: []string{getter}, FieldSorts: []*smt.Sort{s}}
	}
	ts.celValueSort = c.MkDatatypeSort("CelValue", []smt.ConstructorSpec{
		field("Bool", "isBool", "getBool", c.BoolSort()),
		field("Int", "isInt", "getInt", c.IntSort()),
		field("Uint", "isUint", "getUint", c.IntSort()),
		field("Double", "isDouble", "getDouble", fp),
		field("String", "isString", "getString", c.StringSort()),
		field("Bytes", "isBytes", "getBytes", c.StringSort()),
		field("Timestamp", "isTimestamp", "getTimestamp", c.IntSort()),
		field("Duration", "isDuration", "getDuration", c.IntSort()),
		{Name: "CelError", TesterName: "isError"},
		field("CelUnknown", "isUnknown", "getUnknownId", ts.unknownIDSort),
		field("Optional", "isOptional", "getOptionalRef", ts.optionalRefSort),
		field("List", "isList", "getListRef", ts.listRefSort),
		field("Map", "isMap", "getMapRef", ts.mapRefSort),
		field("Message", "isMessage", "getMessageRef", ts.messageRefSort),
		{Name: "CelNull", TesterName: "isNull"},
	})
	k := ts.celValueSort.Datatype.Constructors
	ts.boolCons, ts.intCons, ts.uintCons, ts.doubleCons = k[0], k[1], k[2], k[3]
	ts.stringCons, ts.bytesCons, ts.timestampCons, ts.durationCons = k[4], k[5], k[6], k[7]
	ts.errorCons, ts.unknownCons, ts.optionalCons, ts.listCons = k[8], k[9], k[10], k[11]
	ts.mapCons, ts.messageCons, ts.nullCons = k[12], k[13], k[14]

	cv := ts.celValueSort
	s := func(sorts ...*smt.Sort) []*smt.Sort { return sorts }
	ts.optionalValueFunc = c.MkFuncDecl("opt_value", s(ts.optionalRefSort), cv)
	ts.optionalOfRefFunc = c.MkFuncDecl("!optionalOfRef", s(cv), ts.optionalRefSort)
	ts.asSeqFunc = c.MkFuncDecl("as_seq", s(ts.listRefSort), c.SeqSort(cv))
	ts.mapValuesFunc = c.MkFuncDecl("map_values", s(ts.mapRefSort), c.ArraySort(cv, cv))
	ts.mapKeysFunc = c.MkFuncDecl("map_keys", s(ts.mapRefSort), c.SeqSort(cv))
	ts.mapPresenceFunc = c.MkFuncDecl("map_presence", s(ts.mapRefSort), c.ArraySort(cv, c.BoolSort()))
	ts.msgValuesFunc = c.MkFuncDecl("msg_values", s(ts.messageRefSort), c.ArraySort(c.StringSort(), cv))
	ts.msgPresenceFunc = c.MkFuncDecl("msg_presence", s(ts.messageRefSort), c.ArraySort(c.StringSort(), c.BoolSort()))
	ts.msgTypeNameFunc = c.MkFuncDecl("msg_type_name", s(ts.messageRefSort), c.StringSort())
	ts.hasTruncatedTypeConstraintFunc = c.MkFuncDecl("!has_truncated_type_constraint", s(cv), c.BoolSort())
	ts.truncateDoubleFunc = c.MkFuncDecl("!truncate_double", s(fp), c.IntSort())
	ts.hasFractionFunc = c.MkFuncDecl("!has_fraction", s(fp), c.BoolSort())
	return ts
}

// Ctx returns the context of the type system.
func (ts *TypeSystem) Ctx() *smt.Context { return ts.c }

// CelValueSort returns the datatype sort of CEL values.
func (ts *TypeSystem) CelValueSort() *smt.Sort { return ts.celValueSort }

// ListRefSort returns the uninterpreted sort of list references.
func (ts *TypeSystem) ListRefSort() *smt.Sort { return ts.listRefSort }

// MapRefSort returns the uninterpreted sort of map references.
func (ts *TypeSystem) MapRefSort() *smt.Sort { return ts.mapRefSort }

// MessageRefSort returns the uninterpreted sort of message references.
func (ts *TypeSystem) MessageRefSort() *smt.Sort { return ts.messageRefSort }

// MkListRefConst returns a fresh list reference.
func (ts *TypeSystem) MkListRefConst(prefix string) *smt.Term {
	return ts.c.MkFreshConst(prefix, ts.listRefSort)
}

// MkMapRefConst returns a fresh map reference.
func (ts *TypeSystem) MkMapRefConst(prefix string) *smt.Term {
	return ts.c.MkFreshConst(prefix, ts.mapRefSort)
}

// MkMessageRefConst returns a fresh message reference.
func (ts *TypeSystem) MkMessageRefConst(prefix string) *smt.Term {
	return ts.c.MkFreshConst(prefix, ts.messageRefSort)
}

// InternFuncDecl returns the function with the given name and signature.
func (ts *TypeSystem) InternFuncDecl(name string, domain []*smt.Sort, rng *smt.Sort) *smt.FuncDecl {
	return ts.c.MkFuncDecl(name, domain, rng)
}

func (ts *TypeSystem) cons(k *smt.Constructor, arg *smt.Term) *smt.Term { return ts.c.MkApp(k.Decl, arg) }
func (ts *TypeSystem) test(k *smt.Constructor, v *smt.Term) *smt.Term   { return ts.c.MkApp(k.Tester, v) }
func (ts *TypeSystem) get(k *smt.Constructor, v *smt.Term) *smt.Term    { return ts.c.MkApp(k.Accessors[0], v) }

// MkBool returns the CEL bool b.
func (ts *TypeSystem) MkBool(b bool) *smt.Term { return ts.cons(ts.boolCons, ts.c.MkBool(b)) }

// WrapBool wraps a Bool term.
func (ts *TypeSystem) WrapBool(e *smt.Term) *smt.Term { return ts.cons(ts.boolCons, e) }

// WrapInt wraps an Int term as a CEL int.
func (ts *TypeSystem) WrapInt(e *smt.Term) *smt.Term { return ts.cons(ts.intCons, e) }

// WrapString wraps a String term.
func (ts *TypeSystem) WrapString(e *smt.Term) *smt.Term { return ts.cons(ts.stringCons, e) }

// WrapUint wraps an Int term as a CEL uint.
func (ts *TypeSystem) WrapUint(e *smt.Term) *smt.Term { return ts.cons(ts.uintCons, e) }

// WrapDouble wraps a double, mapping every NaN to the canonical NaN.
func (ts *TypeSystem) WrapDouble(e *smt.Term) *smt.Term {
	c := ts.c
	return ts.cons(ts.doubleCons, c.MkITE(c.MkFPIsNaN(e), c.MkFPNaN(c.FPSortDouble()), e))
}

// WrapBytes wraps a String term as CEL bytes.
func (ts *TypeSystem) WrapBytes(e *smt.Term) *smt.Term { return ts.cons(ts.bytesCons, e) }

// WrapTimestamp wraps nanoseconds since the epoch as a timestamp.
func (ts *TypeSystem) WrapTimestamp(e *smt.Term) *smt.Term { return ts.cons(ts.timestampCons, e) }

// WrapDuration wraps nanoseconds as a duration.
func (ts *TypeSystem) WrapDuration(e *smt.Term) *smt.Term { return ts.cons(ts.durationCons, e) }

// MkInt returns the CEL int v.
func (ts *TypeSystem) MkInt(v int64) *smt.Term { return ts.cons(ts.intCons, ts.c.MkInt(v)) }

// MkUint returns the CEL uint written in decimal in v.
func (ts *TypeSystem) MkUint(v string) *smt.Term { return ts.cons(ts.uintCons, ts.c.MkIntString(v)) }

// MkUint64 returns the CEL uint v.
func (ts *TypeSystem) MkUint64(v uint64) *smt.Term { return ts.MkUint(strconv.FormatUint(v, 10)) }

// MkDouble returns the CEL double v.
func (ts *TypeSystem) MkDouble(v float64) *smt.Term { return ts.cons(ts.doubleCons, ts.MkFpDouble(v)) }

// MkFpDouble returns the floating point literal v.
func (ts *TypeSystem) MkFpDouble(v float64) *smt.Term { return ts.c.MkFP(v, ts.c.FPSortDouble()) }

// IsDouble tests for a double.
func (ts *TypeSystem) IsDouble(v *smt.Term) *smt.Term { return ts.test(ts.doubleCons, v) }

// GetDouble extracts a double.
func (ts *TypeSystem) GetDouble(v *smt.Term) *smt.Term { return ts.get(ts.doubleCons, v) }

// StructuralEquality returns whether two CEL values are equal, comparing the
// contents of lists, maps and messages, and doubles with IEEE 754 equality.
func (ts *TypeSystem) StructuralEquality(a0, a1 *smt.Term) *smt.Term {
	c := ts.c
	isListEq := c.MkAnd(ts.IsList(a0), ts.IsList(a1))
	seqEq := c.MkEq(ts.GetSeq(ts.GetListRef(a0)), ts.GetSeq(ts.GetListRef(a1)))

	isMapEq := c.MkAnd(ts.IsMap(a0), ts.IsMap(a1))
	m0, m1 := ts.GetMapRef(a0), ts.GetMapRef(a1)
	mapEq := c.MkAnd(
		c.MkEq(ts.GetMapPresence(m0), ts.GetMapPresence(m1)),
		c.MkEq(ts.GetMapValues(m0), ts.GetMapValues(m1)))

	isMsgEq := c.MkAnd(ts.IsMessage(a0), ts.IsMessage(a1))
	r0, r1 := ts.GetMessageRef(a0), ts.GetMessageRef(a1)
	msgEq := c.MkAnd(
		c.MkEq(ts.GetMsgTypeName(r0), ts.GetMsgTypeName(r1)),
		c.MkEq(ts.GetMsgValues(r0), ts.GetMsgValues(r1)),
		c.MkEq(ts.GetMsgPresence(r0), ts.GetMsgPresence(r1)))

	isDoubleEq := c.MkAnd(ts.IsDouble(a0), ts.IsDouble(a1))
	doubleEq := c.MkFPEq(ts.GetDouble(a0), ts.GetDouble(a1))

	genericEq := c.MkEq(a0, a1)
	return NewSwitch(c).
		Case(isListEq, seqEq).
		Case(isMapEq, mapEq).
		Case(isMsgEq, msgEq).
		Case(isDoubleEq, doubleEq).
		Build(genericEq)
}

// MkString returns the CEL string s.
func (ts *TypeSystem) MkString(s string) *smt.Term { return ts.cons(ts.stringCons, MkZ3String(ts.c, s)) }

// MkBytes returns CEL bytes whose UTF-8 decoding is s.
func (ts *TypeSystem) MkBytes(s string) *smt.Term { return ts.cons(ts.bytesCons, MkZ3String(ts.c, s)) }

// MkZ3String builds a string literal the way the Z3 Java API's mkString does:
// it escapes every code point outside printable ASCII as \u{...}, and Z3 then
// decodes all \u escapes, including any already present in s.
func MkZ3String(c *smt.Context, s string) *smt.Term {
	var escaped []rune
	for _, r := range s {
		if r <= 32 || r > 127 {
			escaped = append(escaped, []rune(fmt.Sprintf(`\u{%x}`, r))...)
		} else {
			escaped = append(escaped, r)
		}
	}
	e, err := smt.ParseSExpr(smt.QuoteString(nil)[:1] + escapeQuotes(string(escaped)) + `"`)
	if err != nil {
		return c.MkString(s)
	}
	return c.MkStringRunes(e.Runes)
}

func escapeQuotes(s string) string {
	out := make([]rune, 0, len(s))
	for _, r := range s {
		out = append(out, r)
		if r == '"' {
			out = append(out, '"')
		}
	}
	return string(out)
}

// Wrap applies a constructor.
func (ts *TypeSystem) wrap(k *smt.Constructor, e *smt.Term) *smt.Term { return ts.cons(k, e) }

// MkError returns the CEL error value.
func (ts *TypeSystem) MkError() *smt.Term { return ts.c.MkApp(ts.errorCons.Decl) }

// MkNull returns null.
func (ts *TypeSystem) MkNull() *smt.Term { return ts.c.MkApp(ts.nullCons.Decl) }

// MkUnknown returns the generic unknown.
func (ts *TypeSystem) MkUnknown() *smt.Term {
	return ts.mkUnknown(ts.c.MkConst(genericUnknownID, ts.unknownIDSort))
}

func (ts *TypeSystem) mkUnknown(id *smt.Term) *smt.Term { return ts.cons(ts.unknownCons, id) }

// mkParameterizedUnknown returns an unknown whose id is the uninterpreted
// function name applied to args, so that only unknowns produced by the same
// operation over the same arguments are equal.
func (ts *TypeSystem) mkParameterizedUnknown(name string, args []*smt.Term) *smt.Term {
	domain := make([]*smt.Sort, len(args))
	for i := range domain {
		domain[i] = ts.celValueSort
	}
	uf := ts.InternFuncDecl(name, domain, ts.unknownIDSort)
	return ts.mkUnknown(ts.c.MkApp(uf, args...))
}

func (ts *TypeSystem) isParameterizingUnknowns() bool { return ts.parameterizeUnknowns }

// propagateErrorAndUnknown short-circuits result to unknown, or else error, if
// any of checkArgs is. allArgs key the parameterized unknown.
func (ts *TypeSystem) propagateErrorAndUnknown(opName string, result *smt.Term, checkArgs, allArgs []*smt.Term) *smt.Term {
	if len(checkArgs) == 0 {
		return result
	}
	c := ts.c
	errs := make([]*smt.Term, len(checkArgs))
	unks := make([]*smt.Term, len(checkArgs))
	for i, a := range checkArgs {
		errs[i] = ts.IsError(a)
		unks[i] = ts.IsUnknown(a)
	}
	var unknownResult *smt.Term
	if ts.parameterizeUnknowns {
		unknownResult = ts.mkParameterizedUnknown(opName, allArgs)
	} else {
		unknownResult = ts.MkUnknown()
	}
	hasError := c.MkOr(errs...)
	hasUnknown := c.MkOr(unks...)
	return NewSwitch(c).Case(hasUnknown, unknownResult).Case(hasError, ts.MkError()).Build(result)
}

// WithRuntimeError makes result an error wherever one of conditions holds.
func (ts *TypeSystem) WithRuntimeError(result *smt.Term, first *smt.Term, rest ...*smt.Term) *smt.Term {
	cond := first
	if len(rest) > 0 {
		cond = ts.c.MkOr(append([]*smt.Term{first}, rest...)...)
	}
	return ts.c.MkITE(cond, ts.MkError(), result)
}

// IsError tests for an error.
func (ts *TypeSystem) IsError(v *smt.Term) *smt.Term { return ts.test(ts.errorCons, v) }

// IsUnknown tests for an unknown.
func (ts *TypeSystem) IsUnknown(v *smt.Term) *smt.Term { return ts.test(ts.unknownCons, v) }

// IsErrorOrUnknown tests for an error or unknown.
func (ts *TypeSystem) IsErrorOrUnknown(v *smt.Term) *smt.Term {
	return ts.c.MkOr(ts.IsError(v), ts.IsUnknown(v))
}

// IsBool tests for a bool.
func (ts *TypeSystem) IsBool(v *smt.Term) *smt.Term { return ts.test(ts.boolCons, v) }

// UnwrapBool extracts a bool.
func (ts *TypeSystem) UnwrapBool(v *smt.Term) *smt.Term { return ts.get(ts.boolCons, v) }

// MkOptionalNone returns optional.none().
func (ts *TypeSystem) MkOptionalNone() *smt.Term { return ts.cons(ts.optionalCons, ts.MkNoneOptionalRef()) }

// MkNoneOptionalRef returns the reference of the empty optional.
func (ts *TypeSystem) MkNoneOptionalRef() *smt.Term {
	return ts.c.MkConst("!optionalNoneRef", ts.optionalRefSort)
}

// MkOptionalOf wraps an optional reference.
func (ts *TypeSystem) MkOptionalOf(ref *smt.Term) *smt.Term { return ts.cons(ts.optionalCons, ref) }

// OptionalOfRefFunc returns the function giving the optional reference of a value.
func (ts *TypeSystem) OptionalOfRefFunc() *smt.FuncDecl { return ts.optionalOfRefFunc }

// IsOptional tests for an optional.
func (ts *TypeSystem) IsOptional(v *smt.Term) *smt.Term { return ts.test(ts.optionalCons, v) }

// GetOptionalRef extracts an optional reference.
func (ts *TypeSystem) GetOptionalRef(v *smt.Term) *smt.Term { return ts.get(ts.optionalCons, v) }

func (ts *TypeSystem) isOptionalRefAccessor(t *smt.Term) bool {
	return t.IsAppOf(ts.optionalCons.Accessors[0])
}

// OptHasValue tests whether an optional reference holds a value.
func (ts *TypeSystem) OptHasValue(ref *smt.Term) *smt.Term {
	return ts.c.MkNot(ts.c.MkEq(ref, ts.MkNoneOptionalRef()))
}

// GetOptionalValue returns the value of an optional reference.
func (ts *TypeSystem) GetOptionalValue(ref *smt.Term) *smt.Term {
	return ts.c.MkApp(ts.optionalValueFunc, ref)
}

// IsInt tests for an int.
func (ts *TypeSystem) IsInt(v *smt.Term) *smt.Term { return ts.test(ts.intCons, v) }

// GetInt extracts an int.
func (ts *TypeSystem) GetInt(v *smt.Term) *smt.Term { return ts.get(ts.intCons, v) }

// IsUint tests for a uint.
func (ts *TypeSystem) IsUint(v *smt.Term) *smt.Term { return ts.test(ts.uintCons, v) }

// GetUint extracts a uint.
func (ts *TypeSystem) GetUint(v *smt.Term) *smt.Term { return ts.get(ts.uintCons, v) }

// IsTimestamp tests for a timestamp.
func (ts *TypeSystem) IsTimestamp(v *smt.Term) *smt.Term { return ts.test(ts.timestampCons, v) }

// GetTimestamp extracts a timestamp's nanoseconds since the epoch.
func (ts *TypeSystem) GetTimestamp(v *smt.Term) *smt.Term { return ts.get(ts.timestampCons, v) }

// IsDuration tests for a duration.
func (ts *TypeSystem) IsDuration(v *smt.Term) *smt.Term { return ts.test(ts.durationCons, v) }

// GetDuration extracts a duration's nanoseconds.
func (ts *TypeSystem) GetDuration(v *smt.Term) *smt.Term { return ts.get(ts.durationCons, v) }

// IsString tests for a string.
func (ts *TypeSystem) IsString(v *smt.Term) *smt.Term { return ts.test(ts.stringCons, v) }

// IsBytes tests for bytes.
func (ts *TypeSystem) IsBytes(v *smt.Term) *smt.Term { return ts.test(ts.bytesCons, v) }

// GetString extracts a string.
func (ts *TypeSystem) GetString(v *smt.Term) *smt.Term { return ts.get(ts.stringCons, v) }

// GetBytes extracts bytes.
func (ts *TypeSystem) GetBytes(v *smt.Term) *smt.Term { return ts.get(ts.bytesCons, v) }

// IsPrimitiveKey tests for a value of a valid map key kind.
func (ts *TypeSystem) IsPrimitiveKey(v *smt.Term) *smt.Term {
	return ts.c.MkOr(ts.IsBool(v), ts.IsInt(v), ts.IsUint(v), ts.IsString(v), ts.IsBytes(v))
}

// IsStruct tests for a message.
func (ts *TypeSystem) IsStruct(v *smt.Term) *smt.Term { return ts.IsMessage(v) }

// IsNull tests for null.
func (ts *TypeSystem) IsNull(v *smt.Term) *smt.Term { return ts.test(ts.nullCons, v) }

// WrapList wraps a list reference.
func (ts *TypeSystem) WrapList(ref *smt.Term) *smt.Term { return ts.cons(ts.listCons, ref) }

// IsList tests for a list.
func (ts *TypeSystem) IsList(v *smt.Term) *smt.Term { return ts.test(ts.listCons, v) }

// GetListRef extracts a list reference.
func (ts *TypeSystem) GetListRef(v *smt.Term) *smt.Term { return ts.get(ts.listCons, v) }

// GetSeq returns the elements of a list reference.
func (ts *TypeSystem) GetSeq(ref *smt.Term) *smt.Term { return ts.c.MkApp(ts.asSeqFunc, ref) }

// WrapMap wraps a map reference.
func (ts *TypeSystem) WrapMap(ref *smt.Term) *smt.Term { return ts.cons(ts.mapCons, ref) }

// IsMap tests for a map.
func (ts *TypeSystem) IsMap(v *smt.Term) *smt.Term { return ts.test(ts.mapCons, v) }

// GetMapRef extracts a map reference.
func (ts *TypeSystem) GetMapRef(v *smt.Term) *smt.Term { return ts.get(ts.mapCons, v) }

// GetMapValues returns the values of a map reference.
func (ts *TypeSystem) GetMapValues(ref *smt.Term) *smt.Term { return ts.c.MkApp(ts.mapValuesFunc, ref) }

// GetMapKeys returns the key sequence of a map reference.
func (ts *TypeSystem) GetMapKeys(ref *smt.Term) *smt.Term { return ts.c.MkApp(ts.mapKeysFunc, ref) }

// GetMapPresence returns the key presence of a map reference.
func (ts *TypeSystem) GetMapPresence(ref *smt.Term) *smt.Term {
	return ts.c.MkApp(ts.mapPresenceFunc, ref)
}

// WrapMessage wraps a message reference.
func (ts *TypeSystem) WrapMessage(ref *smt.Term) *smt.Term { return ts.cons(ts.messageCons, ref) }

// IsMessage tests for a message.
func (ts *TypeSystem) IsMessage(v *smt.Term) *smt.Term { return ts.test(ts.messageCons, v) }

// GetMessageRef extracts a message reference.
func (ts *TypeSystem) GetMessageRef(v *smt.Term) *smt.Term { return ts.get(ts.messageCons, v) }

// GetMsgValues returns the field values of a message reference.
func (ts *TypeSystem) GetMsgValues(ref *smt.Term) *smt.Term { return ts.c.MkApp(ts.msgValuesFunc, ref) }

// GetMsgPresence returns the field presence of a message reference.
func (ts *TypeSystem) GetMsgPresence(ref *smt.Term) *smt.Term {
	return ts.c.MkApp(ts.msgPresenceFunc, ref)
}

// GetMsgTypeName returns the type name of a message reference.
func (ts *TypeSystem) GetMsgTypeName(ref *smt.Term) *smt.Term {
	return ts.c.MkApp(ts.msgTypeNameFunc, ref)
}

// hasTruncatedTypeConstraint is whether val is, or was built from, a container
// whose type constraint was truncated at the unroll limit.
func (ts *TypeSystem) hasTruncatedTypeConstraint(v *smt.Term) *smt.Term {
	return ts.c.MkApp(ts.hasTruncatedTypeConstraintFunc, v)
}

// CheckIntOverflow tests whether an integer is outside int64.
func (ts *TypeSystem) CheckIntOverflow(r *smt.Term) *smt.Term {
	c := ts.c
	return c.MkOr(c.MkGt(r, c.MkIntString(MaxInt64)), c.MkLt(r, c.MkIntString(MinInt64)))
}

// CheckTimestampOverflow tests whether nanoseconds since the epoch are outside CEL's timestamp range.
func (ts *TypeSystem) CheckTimestampOverflow(r *smt.Term) *smt.Term {
	c := ts.c
	return c.MkOr(c.MkGt(r, c.MkIntString(maxTimestampNanos)), c.MkLt(r, c.MkIntString(minTimestampNanos)))
}

// CheckDurationOverflow tests whether nanoseconds are outside CEL's duration range.
func (ts *TypeSystem) CheckDurationOverflow(r *smt.Term) *smt.Term {
	c := ts.c
	return c.MkOr(c.MkGt(r, c.MkIntString(maxTotalDurationNanos)), c.MkLt(r, c.MkIntString(minTotalDurationNanos)))
}

// CheckUintOverflow tests whether an integer is outside uint64.
func (ts *TypeSystem) CheckUintOverflow(r *smt.Term) *smt.Term {
	c := ts.c
	return c.MkOr(c.MkGt(r, c.MkIntString(MaxUint64)), c.MkLt(r, c.MkInt(0)))
}

// isValidScalar holds for values CEL can produce for their kind.
func (ts *TypeSystem) isValidScalar(v *smt.Term) *smt.Term {
	c := ts.c
	d := ts.GetDouble(v)
	return MkAndFlattened(c,
		c.MkImplies(ts.IsInt(v), c.MkNot(ts.CheckIntOverflow(ts.GetInt(v)))),
		c.MkImplies(ts.IsUint(v), c.MkNot(ts.CheckUintOverflow(ts.GetUint(v)))),
		c.MkImplies(c.MkAnd(ts.IsDouble(v), c.MkFPIsNaN(d)), c.MkEq(v, ts.WrapDouble(d))),
		c.MkImplies(ts.IsTimestamp(v), c.MkNot(ts.CheckTimestampOverflow(ts.GetTimestamp(v)))),
		c.MkImplies(ts.IsDuration(v), c.MkNot(ts.CheckDurationOverflow(ts.GetDuration(v)))))
}

// IsValidValue holds for CEL values: neither errors nor unknowns, and in range.
func (ts *TypeSystem) IsValidValue(v *smt.Term) *smt.Term {
	return ts.c.MkAnd(ts.c.MkNot(ts.IsErrorOrUnknown(v)), ts.isValidScalar(v))
}

// EqualKey is a key a map lookup may find, and when.
type EqualKey struct {
	Key, Cond *smt.Term
}

// equalKeys returns the keys a lookup of key finds: key itself, and its numeric
// counterparts across int, uint and double.
func (ts *TypeSystem) equalKeys(key *smt.Term) []EqualKey {
	c := ts.c
	keys := []EqualKey{{key, c.MkTrue()}}
	isInt := ts.IsInt(key)
	keys = ts.addEqualKey(keys, ts.WrapUint(ts.GetInt(key)), c.MkAnd(isInt, c.MkGe(ts.GetInt(key), c.MkInt(0))))
	isUint := ts.IsUint(key)
	keys = ts.addEqualKey(keys, ts.WrapInt(ts.GetUint(key)), c.MkAnd(isUint, c.MkLe(ts.GetUint(key), c.MkIntString(MaxInt64))))
	isDouble := ts.IsDouble(key)
	if !c.Simplify(isDouble).IsFalse() {
		d := c.MkITE(isDouble, ts.GetDouble(key), ts.MkFpDouble(0.0))
		t := ts.truncateDouble(d)
		isIntegralDouble := c.MkAnd(isDouble, ts.isIntegral(d))
		keys = ts.addEqualKey(keys, ts.WrapInt(t), c.MkAnd(isIntegralDouble, c.MkNot(ts.CheckIntOverflow(t))))
		keys = ts.addEqualKey(keys, ts.WrapUint(t), c.MkAnd(isIntegralDouble, c.MkGe(t, c.MkInt(0))))
	}
	return keys
}

func (ts *TypeSystem) addEqualKey(keys []EqualKey, key, cond *smt.Term) []EqualKey {
	s := ts.c.Simplify(cond)
	if s.IsFalse() {
		return keys
	}
	if s.IsTrue() {
		cond = s
	}
	return append(keys, EqualKey{key, cond})
}

// HasEqualKey tests whether map has a key equal to key.
func (ts *TypeSystem) HasEqualKey(m, key *smt.Term) *smt.Term {
	return ts.hasEqualKey(m, ts.equalKeys(key))
}

func (ts *TypeSystem) hasEqualKey(m *smt.Term, keys []EqualKey) *smt.Term {
	presence := ts.GetMapPresence(ts.GetMapRef(m))
	terms := make([]*smt.Term, len(keys))
	for i, k := range keys {
		terms[i] = ts.isPresent(presence, k)
	}
	return MkOrFlattened(ts.c, terms...)
}

func (ts *TypeSystem) valueAtEqualKey(m *smt.Term, keys []EqualKey) *smt.Term {
	ref := ts.GetMapRef(m)
	presence := ts.GetMapPresence(ref)
	values := ts.GetMapValues(ref)
	sw := NewSwitch(ts.c)
	for _, k := range keys {
		sw.Case(ts.isPresent(presence, k), ts.c.MkSelect(values, k.Key))
	}
	return sw.Build(ts.MkUnknown())
}

func (ts *TypeSystem) isPresent(presence *smt.Term, k EqualKey) *smt.Term {
	return MkAndFlattened(ts.c, k.Cond, ts.c.MkSelect(presence, k.Key))
}

// intEqDouble tests whether the integer n equals the double d.
func (ts *TypeSystem) intEqDouble(n, d *smt.Term) *smt.Term {
	return ts.c.MkAnd(ts.isIntegral(d), ts.c.MkEq(n, ts.truncateDouble(d)))
}

// IntLtDouble tests whether the integer n is less than the double d.
func (ts *TypeSystem) IntLtDouble(n, d *smt.Term) *smt.Term {
	c := ts.c
	if exact, ok := ts.asExactDouble(n); ok {
		return c.MkFPLt(exact, d)
	}
	t := ts.truncateDouble(d)
	return c.MkOr(
		c.MkFPGEq(d, ts.MkFpDouble(twoTo64)),
		c.MkAnd(
			ts.isBelowTwoTo64(d),
			c.MkOr(
				c.MkLt(n, t),
				c.MkAnd(c.MkEq(n, t), ts.hasFraction(d), c.MkNot(c.MkFPIsNegative(d))))))
}

// DoubleLtInt tests whether the double d is less than the integer n.
func (ts *TypeSystem) DoubleLtInt(d, n *smt.Term) *smt.Term {
	c := ts.c
	if exact, ok := ts.asExactDouble(n); ok {
		return c.MkFPLt(d, exact)
	}
	t := ts.truncateDouble(d)
	return c.MkOr(
		c.MkFPLEq(d, c.MkFPNeg(ts.MkFpDouble(twoTo64))),
		c.MkAnd(
			ts.isBelowTwoTo64(d),
			c.MkOr(
				c.MkLt(t, n),
				c.MkAnd(c.MkEq(n, t), ts.hasFraction(d), c.MkFPIsNegative(d)))))
}

// IntLeDouble tests whether the integer n is at most the double d.
func (ts *TypeSystem) IntLeDouble(n, d *smt.Term) *smt.Term {
	c := ts.c
	return c.MkAnd(c.MkNot(c.MkFPIsNaN(d)), c.MkNot(ts.DoubleLtInt(d, n)))
}

// DoubleLeInt tests whether the double d is at most the integer n.
func (ts *TypeSystem) DoubleLeInt(d, n *smt.Term) *smt.Term {
	c := ts.c
	return c.MkAnd(c.MkNot(c.MkFPIsNaN(d)), c.MkNot(ts.IntLtDouble(n, d)))
}

// asExactDouble returns the double equal to n, if n is a constant a double holds exactly.
func (ts *TypeSystem) asExactDouble(n *smt.Term) (*smt.Term, bool) {
	s := ts.c.Simplify(n)
	if s.Op != smt.OpIntLit {
		return nil, false
	}
	f, acc := new(big.Float).SetInt(s.Int).Float64()
	if acc != big.Exact || math.IsInf(f, 0) {
		return nil, false
	}
	return ts.MkFpDouble(f), true
}

func (ts *TypeSystem) isIntegral(d *smt.Term) *smt.Term {
	return ts.c.MkAnd(ts.isBelowTwoTo64(d), ts.c.MkNot(ts.hasFraction(d)))
}

func (ts *TypeSystem) truncateDouble(d *smt.Term) *smt.Term {
	c := ts.c
	return c.MkITE(c.MkFPIsZero(d), c.MkInt(0), ts.applyUndefined(ts.truncateDoubleFunc, d))
}

// defineDoublesContradictedBy returns exact definitions for the tracked doubles
// whose truncation or fraction m gets wrong.
func (ts *TypeSystem) defineDoublesContradictedBy(m smt.Model) ([]*smt.Term, error) {
	c := ts.c
	var defs []*smt.Term
	kept := ts.undefinedDoubles[:0:0]
	for _, d := range ts.undefinedDoubles {
		dv, err := m.Eval(d, true)
		if err != nil {
			return nil, err
		}
		value, err := ts.toFloat64(dv)
		if err != nil {
			return nil, err
		}
		if math.IsNaN(value) || value == 0 || math.Abs(value) >= twoTo64 {
			kept = append(kept, d)
			continue
		}
		tv, err := m.Eval(c.MkApp(ts.truncateDoubleFunc, d), true)
		if err != nil {
			return nil, err
		}
		fv, err := m.Eval(c.MkApp(ts.hasFractionFunc, d), true)
		if err != nil {
			return nil, err
		}
		if tv.Op != smt.OpIntLit {
			return nil, fmt.Errorf("verifier: truncation evaluated to %s", tv)
		}
		trunc, _ := new(big.Float).SetFloat64(math.Trunc(value)).Int(nil)
		isInteger := value == math.Trunc(value)
		if tv.Int.Cmp(trunc) != 0 || fv.IsTrue() == isInteger {
			delete(ts.undefinedDoublesSeen, d)
			defs = append(defs, ts.defineDouble(d))
			continue
		}
		kept = append(kept, d)
	}
	ts.undefinedDoubles = kept
	return defs, nil
}

// toFloat64 converts an evaluated floating point literal to a float64.
func (ts *TypeSystem) toFloat64(t *smt.Term) (float64, error) {
	if t.Op != smt.OpFPLit {
		return 0, fmt.Errorf("verifier: expected a double, got %s", t)
	}
	return math.Float64frombits(t.Bits), nil
}

func (ts *TypeSystem) hasFraction(d *smt.Term) *smt.Term {
	c := ts.c
	return c.MkAnd(c.MkNot(c.MkFPIsZero(d)), ts.applyUndefined(ts.hasFractionFunc, d))
}

func (ts *TypeSystem) applyUndefined(f *smt.FuncDecl, d *smt.Term) *smt.Term {
	if !ts.undefinedDoublesSeen[d] {
		ts.undefinedDoublesSeen[d] = true
		ts.undefinedDoubles = append(ts.undefinedDoubles, d)
	}
	return ts.c.MkApp(f, d)
}

func (ts *TypeSystem) defineDouble(d *smt.Term) *smt.Term {
	c := ts.c
	// 65-bit two's complement holds every truncation below 2^64.
	truncated := c.MkBV2Int(c.MkFPToBV(c.MkFPRoundTowardZero(), d, 65, true), true)
	hasFraction := c.MkNot(c.MkFPEq(d, c.MkFPRoundToIntegral(c.MkFPRoundTowardZero(), d)))
	return c.MkImplies(
		ts.isBelowTwoTo64(d),
		c.MkAnd(
			c.MkEq(c.MkApp(ts.truncateDoubleFunc, d), truncated),
			c.MkEq(c.MkApp(ts.hasFractionFunc, d), hasFraction)))
}

func (ts *TypeSystem) isBelowTwoTo64(d *smt.Term) *smt.Term {
	return ts.c.MkFPLt(ts.c.MkFPAbs(d), ts.MkFpDouble(twoTo64))
}

// MkConcatSafe concatenates two sequences.
func (ts *TypeSystem) MkConcatSafe(a, b *smt.Term) *smt.Term { return ts.c.MkConcat(a, b) }

// Constructors, for the counterexample generator and axioms.

func (ts *TypeSystem) listConsDecl() *smt.FuncDecl    { return ts.listCons.Decl }
func (ts *TypeSystem) mapConsDecl() *smt.FuncDecl     { return ts.mapCons.Decl }
func (ts *TypeSystem) messageConsDecl() *smt.FuncDecl { return ts.messageCons.Decl }
