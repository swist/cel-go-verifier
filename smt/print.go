package smt

import (
	"fmt"
	"math/big"
	"strconv"
	"strings"
)

// Print renders t in SMT-LIB2 syntax, the way Z3 prints it, except that
// subterms are shared with let bindings by reference count rather than Z3's
// heuristics.
func Print(t *Term) string {
	p := newPrinter()
	return p.print(t)
}

// PrintFlat renders t without let bindings.
func PrintFlat(t *Term) string {
	var sb strings.Builder
	p := newPrinter()
	p.write(&sb, t, nil)
	return sb.String()
}

type printer struct {
	alias func(*Term) (string, bool)
}

func newPrinter() *printer { return &printer{} }

func (p *printer) print(t *Term) string {
	// Count references to find shared subterms.
	refs := map[*Term]int{}
	var order []*Term
	var count func(*Term)
	count = func(t *Term) {
		refs[t]++
		if refs[t] > 1 {
			return
		}
		for _, a := range t.Args {
			count(a)
		}
		order = append(order, t)
	}
	count(t)
	names := map[*Term]string{}
	var bindings []*Term
	for _, n := range order {
		if n != t && refs[n] > 1 && len(n.Args) > 0 && n.Op != OpLambda && n.Op != OpForall && n.Op != OpExists && !containsBound(n) {
			bindings = append(bindings, n)
		}
	}
	if len(bindings) == 0 {
		var sb strings.Builder
		p.write(&sb, t, nil)
		return sb.String()
	}
	var sb strings.Builder
	for i, b := range bindings {
		var vb strings.Builder
		p.write(&vb, b, names)
		name := "a!" + strconv.Itoa(i+1)
		sb.WriteString("(let ((" + name + " " + vb.String() + ")) ")
		names[b] = name
	}
	p.write(&sb, t, names)
	sb.WriteString(strings.Repeat(")", len(bindings)))
	return sb.String()
}

func containsBound(t *Term) bool {
	if t.Op == OpVar {
		return true
	}
	for _, a := range t.Args {
		if containsBound(a) {
			return true
		}
	}
	return false
}

var stringOpNames = map[Op]string{
	OpSeqConcat:      "str.++",
	OpSeqLen:         "str.len",
	OpSeqContains:    "str.contains",
	OpSeqPrefix:      "str.prefixof",
	OpSeqSuffix:      "str.suffixof",
	OpSeqIndexOf:     "str.indexof",
	OpSeqLastIndexOf: "str.last_indexof",
	OpSeqExtract:     "str.substr",
	OpSeqAt:          "str.at",
	OpSeqReplace:     "str.replace",
}

func (p *printer) write(sb *strings.Builder, t *Term, names map[*Term]string) {
	if n, ok := names[t]; ok {
		sb.WriteString(n)
		return
	}
	if p.alias != nil {
		if a, ok := p.alias(t); ok {
			sb.WriteString(a)
			return
		}
	}
	args := func() {
		for _, a := range t.Args {
			sb.WriteByte(' ')
			p.write(sb, a, names)
		}
		sb.WriteByte(')')
	}
	switch t.Op {
	case OpTrue, OpFalse:
		sb.WriteString(string(t.Op))
	case OpIntLit:
		writeInt(sb, t.Int)
	case OpStrLit:
		sb.WriteString(QuoteString(t.Runes))
	case OpCharLit:
		fmt.Fprintf(sb, "(_ Char %s)", t.Int)
	case OpFPLit:
		sb.WriteString(fpLiteral(t.Bits, t.Sort))
	case OpBVLit:
		sb.WriteString(bvLiteral(t.Int, t.Sort.Size))
	case OpRM:
		sb.WriteString(rmNames[t.RM])
	case OpApp:
		d := t.Decl
		switch d.Kind {
		case DeclTester:
			sb.WriteString("((_ is " + quoteSymbol(d.Cons.Name) + ")")
			args()
			return
		}
		if len(t.Args) == 0 {
			sb.WriteString(quoteSymbol(d.Name))
			return
		}
		sb.WriteString("(" + quoteSymbol(d.Name))
		args()
	case OpModelValue, OpVar:
		sb.WriteString(quoteSymbol(t.Name))
	case OpNeg:
		sb.WriteString("(-")
		args()
	case OpConstArray:
		sb.WriteString("((as const " + t.Sort.String() + ")")
		args()
	case OpAsArray:
		sb.WriteString("(_ as-array " + quoteSymbol(t.Decl.Name) + ")")
	case OpSeqEmpty:
		sb.WriteString("(as seq.empty " + t.Sort.String() + ")")
	case OpLambda, OpForall, OpExists:
		sb.WriteString("(" + string(t.Op) + " (")
		for i, v := range t.Vars {
			if i > 0 {
				sb.WriteByte(' ')
			}
			sb.WriteString("(" + quoteSymbol(v.Name) + " " + v.Sort.String() + ")")
		}
		sb.WriteString(")")
		args()
	case OpOther:
		if strings.HasPrefix(t.Name, "#real:") {
			sb.WriteString(realLiteral(t.Name[len("#real:"):]))
			return
		}
		head := t.Name
		if len(t.Idx) > 0 {
			head = "(_ " + t.Name + idxString(t.Idx) + ")"
		}
		if len(t.Args) == 0 {
			sb.WriteString(head)
			return
		}
		sb.WriteString("(" + head)
		args()
	default:
		name := string(t.Op)
		if len(t.Args) > 0 && t.Args[0].Sort.Kind == KindString {
			if s, ok := stringOpNames[t.Op]; ok {
				name = s
			}
		}
		if len(t.Idx) > 0 {
			name = "(_ " + name + idxString(t.Idx) + ")"
		}
		sb.WriteString("(" + name)
		args()
	}
}

func idxString(idx []int) string {
	var sb strings.Builder
	for _, i := range idx {
		sb.WriteByte(' ')
		sb.WriteString(strconv.Itoa(i))
	}
	return sb.String()
}

func writeInt(sb *strings.Builder, v *big.Int) {
	if v.Sign() < 0 {
		sb.WriteString("(- ")
		sb.WriteString(new(big.Int).Neg(v).String())
		sb.WriteString(")")
		return
	}
	sb.WriteString(v.String())
}

func realLiteral(rat string) string {
	r, _ := new(big.Rat).SetString(rat)
	neg := r.Sign() < 0
	if neg {
		r.Neg(r)
	}
	var s string
	if r.IsInt() {
		s = r.Num().String() + ".0"
	} else {
		s = "(/ " + r.Num().String() + ".0 " + r.Denom().String() + ".0)"
	}
	if neg {
		return "(- " + s + ")"
	}
	return s
}

func fpLiteral(bits uint64, sort *Sort) string {
	eb, sbits := uint(sort.EBits), uint(sort.SBits)
	sign := bits >> (eb + sbits - 1) & 1
	exp := bits >> (sbits - 1) & (uint64(1)<<eb - 1)
	sig := bits & (uint64(1)<<(sbits-1) - 1)
	suffix := fmt.Sprintf(" %d %d)", eb, sbits)
	expMax := uint64(1)<<eb - 1
	switch {
	case exp == expMax && sig != 0:
		return "(_ NaN" + suffix
	case exp == expMax && sign == 0:
		return "(_ +oo" + suffix
	case exp == expMax:
		return "(_ -oo" + suffix
	case exp == 0 && sig == 0 && sign == 0:
		return "(_ +zero" + suffix
	case exp == 0 && sig == 0:
		return "(_ -zero" + suffix
	}
	return fmt.Sprintf("(fp #b%d %s %s)", sign, binLiteral(exp, int(eb)), bitsLiteral(sig, int(sbits-1)))
}

func binLiteral(v uint64, width int) string {
	s := strconv.FormatUint(v, 2)
	return "#b" + strings.Repeat("0", width-len(s)) + s
}

func bitsLiteral(v uint64, width int) string {
	if width%4 == 0 {
		s := strconv.FormatUint(v, 16)
		return "#x" + strings.Repeat("0", width/4-len(s)) + s
	}
	return binLiteral(v, width)
}

func bvLiteral(v *big.Int, width int) string {
	if width%4 == 0 {
		s := v.Text(16)
		return "#x" + strings.Repeat("0", width/4-len(s)) + s
	}
	s := v.Text(2)
	return "#b" + strings.Repeat("0", width-len(s)) + s
}

// QuoteString renders code points as an SMT-LIB2 string literal, escaping like Z3.
func QuoteString(runes []rune) string {
	var sb strings.Builder
	sb.WriteByte('"')
	for _, r := range runes {
		switch {
		case r == '"':
			sb.WriteString(`""`)
		case r == '\\':
			sb.WriteString(`\u{5c}`)
		case r >= 0x20 && r < 0x7f:
			sb.WriteRune(r)
		default:
			fmt.Fprintf(&sb, `\u{%x}`, r)
		}
	}
	sb.WriteByte('"')
	return sb.String()
}

var reservedWords = map[string]bool{
	"let": true, "forall": true, "exists": true, "match": true, "par": true, "as": true, "_": true, "!": true,
	"lambda": true, "NUMERAL": true, "DECIMAL": true, "STRING": true,
}

// quoteSymbol quotes a symbol if it isn't a simple SMT-LIB2 symbol. Like Z3,
// '|' and '\' inside quoted symbols are escaped with a backslash.
func quoteSymbol(s string) string {
	if isSimpleSymbol(s) {
		return s
	}
	var sb strings.Builder
	sb.WriteByte('|')
	for _, r := range s {
		if r == '|' || r == '\\' {
			sb.WriteByte('\\')
		}
		sb.WriteRune(r)
	}
	sb.WriteByte('|')
	return sb.String()
}

func isSimpleSymbol(s string) bool {
	if s == "" || reservedWords[s] {
		return false
	}
	for i, r := range s {
		switch {
		case r >= 'a' && r <= 'z', r >= 'A' && r <= 'Z':
		case r >= '0' && r <= '9':
			if i == 0 {
				return false
			}
		case strings.ContainsRune("~!@$%^&*_-+=<>.?/", r):
		default:
			return false
		}
	}
	return true
}

// DeclareSort renders the declaration of an uninterpreted or datatype sort.
func DeclareSort(s *Sort) string {
	if s.Kind == KindUninterpreted {
		return "(declare-sort " + quoteSymbol(s.Name) + " 0)"
	}
	var sb strings.Builder
	sb.WriteString("(declare-datatypes ((" + quoteSymbol(s.Name) + " 0)) ((")
	for i, k := range s.Datatype.Constructors {
		if i > 0 {
			sb.WriteByte(' ')
		}
		if len(k.FieldNames) == 0 {
			sb.WriteString(quoteSymbol(k.Name))
			continue
		}
		sb.WriteString("(" + quoteSymbol(k.Name))
		for j, f := range k.FieldNames {
			sb.WriteString(" (" + quoteSymbol(f) + " " + k.FieldSorts[j].String() + ")")
		}
		sb.WriteString(")")
	}
	sb.WriteString(")))")
	return sb.String()
}

// DeclareFun renders the declaration of an uninterpreted function.
func DeclareFun(d *FuncDecl) string {
	var sb strings.Builder
	sb.WriteString("(declare-fun " + quoteSymbol(d.Name) + " (")
	for i, s := range d.Domain {
		if i > 0 {
			sb.WriteByte(' ')
		}
		sb.WriteString(s.String())
	}
	sb.WriteString(") " + d.Range.String() + ")")
	return sb.String()
}
