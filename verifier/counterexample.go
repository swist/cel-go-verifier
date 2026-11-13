package verifier

import (
	"fmt"
	"math"
	"math/big"
	"strings"
	"time"
	"unicode"
	"unicode/utf8"

	"cel.dev/cel-go/common/types"
	"cel.dev/cel-go/common/types/ref"

	"github.com/swist/cel-go-verifier/smt"
)

// Witness is an input assignment found by the solver: a counterexample or a satisfying input.
type Witness struct {
	// Names lists the variables in order of first appearance.
	Names []string
	// Variables maps names to values.
	Variables map[string]WitnessVariable
}

// WitnessVariable is the value the solver assigned to one input variable.
type WitnessVariable struct {
	// Value is the value as a CEL runtime value, or nil if it has no exact
	// runtime equivalent (e.g. an unknown).
	Value ref.Val
	// Display is the value as a CEL literal where one exists.
	Display string
}

const maxElementsToPrint = 15

var nanosPerSecondBig = big.NewInt(NanosPerSecond)

type cxValue struct {
	val     ref.Val
	exact   bool
	display string
}

func exactValue(v ref.Val, display string) cxValue { return cxValue{v, true, display} }
func inexactValue(display string) cxValue          { return cxValue{nil, false, display} }

type counterexampleGenerator struct {
	c      *smt.Context
	ts     *TypeSystem
	m      smt.Model
	limit  int
	onPath map[*smt.Term]bool
	err    error
}

func generateWitness(ts *TypeSystem, m smt.Model, limit int, inputs []*smt.Term) (w *Witness, err error) {
	g := &counterexampleGenerator{c: ts.c, ts: ts, m: m, limit: limit, onPath: map[*smt.Term]bool{}}
	w = &Witness{Variables: map[string]WitnessVariable{}}
	for _, in := range inputs {
		v := g.extract(g.eval(in))
		if g.err != nil {
			return nil, g.err
		}
		name := in.Decl.Name
		w.Names = append(w.Names, name)
		w.Variables[name] = WitnessVariable{Value: v.val, Display: v.display}
	}
	return w, nil
}

func (g *counterexampleGenerator) eval(t *smt.Term) *smt.Term {
	if g.err != nil {
		return g.c.MkFalse()
	}
	v, err := g.m.Eval(t, true)
	if err != nil {
		g.err = err
		return g.c.MkFalse()
	}
	return v
}

func (g *counterexampleGenerator) extract(t *smt.Term) cxValue {
	if g.onPath[t] {
		return inexactValue("<cycle>")
	}
	g.onPath[t] = true
	v := g.extractValue(t)
	delete(g.onPath, t)
	return v
}

func (g *counterexampleGenerator) extractValue(t *smt.Term) cxValue {
	ts := g.ts
	if g.err != nil || t.Op != smt.OpApp || t.Decl.Kind != smt.DeclConstructor {
		return inexactValue("?")
	}
	args := t.Args
	switch t.Decl.Cons {
	case ts.intCons:
		v := args[0].Int
		if v.IsInt64() {
			return exactValue(types.Int(v.Int64()), v.String())
		}
		return inexactValue(v.String())
	case ts.uintCons:
		v := args[0].Int
		d := v.String() + "u"
		if v.Sign() >= 0 && v.IsUint64() {
			return exactValue(types.Uint(v.Uint64()), d)
		}
		return inexactValue(d)
	case ts.boolCons:
		return exactValue(types.Bool(args[0].IsTrue()), fmt.Sprint(args[0].IsTrue()))
	case ts.doubleCons:
		f, _ := ts.toFloat64(args[0])
		if math.IsNaN(f) || math.IsInf(f, 0) {
			return exactValue(types.Double(f), `double("`+javaSpecialDouble(f)+`")`)
		}
		return exactValue(types.Double(f), javaDoubleString(f))
	case ts.stringCons:
		return extractString(args[0], false)
	case ts.bytesCons:
		return extractString(args[0], true)
	case ts.timestampCons:
		nanos := args[0].Int
		adj := new(big.Int).Mod(nanos, nanosPerSecondBig)
		secs := new(big.Int).Div(new(big.Int).Sub(nanos, adj), nanosPerSecondBig)
		if !inRange(secs, timestampSecondsMin, timestampSecondsMax) {
			return inexactValue("timestamp(" + secs.String() + ")")
		}
		tm := time.Unix(secs.Int64(), adj.Int64()).UTC()
		return exactValue(types.Timestamp{Time: tm}, `timestamp("`+javaInstantString(secs.Int64(), adj.Int64())+`")`)
	case ts.durationCons:
		secs, rem := new(big.Int).QuoRem(args[0].Int, nanosPerSecondBig, new(big.Int))
		if !inRange(secs, durationSecondsMin, durationSecondsMax) {
			return inexactValue(`duration("` + secs.String() + `s")`)
		}
		s, n := secs.Int64(), rem.Int64()
		display := `duration("` + formatDuration(s, n) + `")`
		// cel-go durations are time.Durations, which cover about ±292 years of CEL's ±10000.
		if s > math.MaxInt64/NanosPerSecond-1 || s < math.MinInt64/NanosPerSecond+1 {
			return inexactValue(display)
		}
		return exactValue(types.Duration{Duration: time.Duration(s)*time.Second + time.Duration(n)}, display)
	case ts.listCons:
		return g.extractList(args[0])
	case ts.mapCons:
		return g.extractMap(args[0])
	case ts.messageCons:
		return g.extractMessage(args[0])
	case ts.errorCons:
		return inexactValue("Error")
	case ts.unknownCons:
		return inexactValue("Unknown")
	case ts.nullCons:
		return exactValue(types.NullValue, "null")
	}
	// Optional is the only remaining constructor.
	if !g.eval(ts.OptHasValue(args[0])).IsTrue() {
		return exactValue(types.OptionalNone, "optional.none()")
	}
	v := g.extract(g.eval(ts.GetOptionalValue(args[0])))
	out := cxValue{display: "optional.of(" + v.display + ")"}
	if v.exact {
		out.exact = true
		out.val = types.OptionalOf(v.val)
	}
	return out
}

func javaSpecialDouble(f float64) string {
	switch {
	case math.IsNaN(f):
		return "NaN"
	case f > 0:
		return "Infinity"
	}
	return "-Infinity"
}

func inRange(v *big.Int, lo, hi int64) bool {
	return v.Cmp(big.NewInt(lo)) >= 0 && v.Cmp(big.NewInt(hi)) <= 0
}

// stringRunes returns the code points of a string value, which models may
// spell as a literal or as a concatenation of units of characters.
func stringRunes(t *smt.Term) []rune {
	switch t.Op {
	case smt.OpStrLit:
		return t.Runes
	case smt.OpCharLit:
		return []rune{rune(t.Int.Int64())}
	case smt.OpSeqUnit:
		return stringRunes(t.Args[0])
	case smt.OpSeqConcat:
		var out []rune
		for _, a := range t.Args {
			out = append(out, stringRunes(a)...)
		}
		return out
	}
	return nil
}

func extractString(t *smt.Term, isBytes bool) cxValue {
	runes := stringRunes(t)
	exact := true
	for _, r := range runes {
		if isBytes && r >= 0x80 || !isBytes && r >= 0xD800 && r <= 0xDFFF {
			exact = false
		}
	}
	display := quoteCEL(runes, isBytes)
	if !exact {
		return inexactValue(display)
	}
	if isBytes {
		return exactValue(types.Bytes(string(runes)), display)
	}
	return exactValue(types.String(string(runes)), display)
}

// quoteCEL renders code points as a CEL string or bytes literal.
func quoteCEL(runes []rune, isBytes bool) string {
	var sb strings.Builder
	if isBytes {
		sb.WriteString(`b"`)
	} else {
		sb.WriteByte('"')
	}
	for _, r := range runes {
		switch {
		case r == '"' || r == '\\':
			sb.WriteByte('\\')
			sb.WriteRune(r)
		case isBytes && (r < 0x20 || r >= 0x7f):
			var buf [utf8.UTFMax]byte
			n := utf8.EncodeRune(buf[:], r)
			for _, b := range buf[:n] {
				fmt.Fprintf(&sb, `\x%02x`, b)
			}
		case isISOControl(r) || (r >= 0xD800 && r <= 0xDFFF):
			fmt.Fprintf(&sb, `\u%04x`, r)
		default:
			sb.WriteRune(r)
		}
	}
	sb.WriteByte('"')
	return sb.String()
}

func isISOControl(r rune) bool { return r <= 0x1f || (r >= 0x7f && r <= 0x9f) && unicode.IsControl(r) }

func (g *counterexampleGenerator) evalLength(t *smt.Term) int64 {
	v := g.eval(t)
	if v.Op != smt.OpIntLit {
		if g.err == nil {
			g.err = fmt.Errorf("verifier: length evaluated to %s", v)
		}
		return 0
	}
	return v.Int.Int64()
}

func (g *counterexampleGenerator) extractList(lref *smt.Term) cxValue {
	c, ts := g.c, g.ts
	length := g.evalLength(c.MkLength(ts.GetSeq(lref)))
	exact := length <= int64(g.limit)
	limit := length
	if !exact {
		limit = min(length, maxElementsToPrint)
	}
	var vals []ref.Val
	var shown []string
	for i := int64(0); i < limit; i++ {
		el := g.extract(g.eval(c.MkNth(ts.GetSeq(lref), c.MkInt(i))))
		if el.exact {
			vals = append(vals, el.val)
		} else {
			exact = false
		}
		shown = append(shown, el.display)
	}
	display := joinShown("[", shown, length, "elements", "]")
	if exact {
		return exactValue(types.NewRefValList(types.DefaultTypeAdapter, vals), display)
	}
	return inexactValue(display)
}

func (g *counterexampleGenerator) extractMap(mref *smt.Term) cxValue {
	c, ts := g.c, g.ts
	length := g.evalLength(c.MkLength(ts.GetMapKeys(mref)))
	exact := length <= int64(g.limit)
	limit := length
	if !exact {
		limit = min(length, maxElementsToPrint)
	}
	vals := map[ref.Val]ref.Val{}
	var shown []string
	seen := map[*smt.Term]bool{}
	keySet := c.MkConstArray(ts.celValueSort, c.MkFalse())
	for i := int64(0); i < limit; i++ {
		key := g.eval(c.MkNth(ts.GetMapKeys(mref), c.MkInt(i)))
		if g.err != nil {
			break
		}
		keySet = c.MkStore(keySet, key, c.MkTrue())
		if seen[key] || !g.eval(c.MkSelect(ts.GetMapPresence(mref), key)).IsTrue() {
			seen[key] = true
			continue
		}
		seen[key] = true
		k := g.extract(key)
		v := g.extract(g.eval(c.MkSelect(ts.GetMapValues(mref), key)))
		if k.exact && v.exact {
			vals[k.val] = v.val
		} else {
			exact = false
		}
		shown = append(shown, k.display+": "+v.display)
	}
	exact = exact && int64(len(seen)) == length && g.eval(c.MkEq(ts.GetMapPresence(mref), keySet)).IsTrue()
	display := joinShown("{", shown, length, "entries", "}")
	if exact {
		return exactValue(types.NewRefValMap(types.DefaultTypeAdapter, vals), display)
	}
	return inexactValue(display)
}

func joinShown(prefix string, shown []string, length int64, noun, suffix string) string {
	out := shown
	if len(out) > maxElementsToPrint {
		out = out[:maxElementsToPrint]
	}
	out = append([]string(nil), out...)
	if length > maxElementsToPrint {
		out = append(out, fmt.Sprintf("... (%d more %s)", length-maxElementsToPrint, noun))
	}
	return prefix + strings.Join(out, ", ") + suffix
}

func (g *counterexampleGenerator) extractMessage(ref *smt.Term) cxValue {
	c, ts := g.c, g.ts
	presence := g.eval(ts.GetMsgPresence(ref))
	typeName := string(stringRunes(g.eval(ts.GetMsgTypeName(ref))))
	var keys []*smt.Term
	seen := map[*smt.Term]bool{}
	for t := presence; t.IsApp() && t.Op == smt.OpStore; t = t.Args[0] {
		if !seen[t.Args[1]] {
			seen[t.Args[1]] = true
			keys = append(keys, t.Args[1])
		}
	}
	var entries []string
	for _, k := range keys {
		if g.eval(c.MkSelect(ts.GetMsgPresence(ref), k)).IsTrue() {
			v := g.eval(c.MkSelect(ts.GetMsgValues(ref), k))
			entries = append(entries, string(stringRunes(k))+": "+g.extract(v).display)
		}
	}
	return inexactValue(typeName + "{" + strings.Join(entries, ", ") + "}")
}
