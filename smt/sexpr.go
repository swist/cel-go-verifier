package smt

import (
	"fmt"
	"strconv"
	"strings"
)

// SExprKind is the kind of an s-expression node.
type SExprKind int

// S-expression kinds.
const (
	SList SExprKind = iota
	// SSymbol is a symbol; Atom holds it unquoted.
	SSymbol
	// SNumeral is a decimal numeral.
	SNumeral
	// SDecimal is a decimal with a fractional part.
	SDecimal
	// SString is a string literal; Runes holds its decoded code points.
	SString
	// SBinary and SHex are bit-vector literals; Atom holds the digits.
	SBinary
	SHex
	// SKeyword is a :keyword.
	SKeyword
)

// SExpr is a parsed s-expression.
type SExpr struct {
	Kind  SExprKind
	Atom  string
	Runes []rune
	List  []*SExpr
}

func (s *SExpr) String() string {
	switch s.Kind {
	case SList:
		parts := make([]string, len(s.List))
		for i, e := range s.List {
			parts[i] = e.String()
		}
		return "(" + strings.Join(parts, " ") + ")"
	case SSymbol:
		return quoteSymbol(s.Atom)
	case SString:
		return QuoteString(s.Runes)
	case SBinary:
		return "#b" + s.Atom
	case SHex:
		return "#x" + s.Atom
	default:
		return s.Atom
	}
}

// IsSymbol reports whether s is the symbol name.
func (s *SExpr) IsSymbol(name string) bool { return s.Kind == SSymbol && s.Atom == name }

// Head returns the symbol at the head of a list, or "".
func (s *SExpr) Head() string {
	if s.Kind == SList && len(s.List) > 0 && s.List[0].Kind == SSymbol {
		return s.List[0].Atom
	}
	return ""
}

// ParseSExprs parses a sequence of s-expressions. Comments start with ';'.
func ParseSExprs(input string) ([]*SExpr, error) {
	r := &sreader{in: input}
	var out []*SExpr
	for {
		r.skip()
		if r.pos >= len(r.in) {
			return out, nil
		}
		e, err := r.read()
		if err != nil {
			return nil, err
		}
		out = append(out, e)
	}
}

// ParseSExpr parses exactly one s-expression.
func ParseSExpr(input string) (*SExpr, error) {
	es, err := ParseSExprs(input)
	if err != nil {
		return nil, err
	}
	if len(es) != 1 {
		return nil, fmt.Errorf("smt: expected one s-expression, got %d", len(es))
	}
	return es[0], nil
}

type sreader struct {
	in  string
	pos int
}

func (r *sreader) skip() {
	for r.pos < len(r.in) {
		c := r.in[r.pos]
		switch {
		case c == ';':
			for r.pos < len(r.in) && r.in[r.pos] != '\n' {
				r.pos++
			}
		case c == ' ' || c == '\t' || c == '\n' || c == '\r':
			r.pos++
		default:
			return
		}
	}
}

func (r *sreader) read() (*SExpr, error) {
	r.skip()
	if r.pos >= len(r.in) {
		return nil, fmt.Errorf("smt: unexpected end of input")
	}
	c := r.in[r.pos]
	switch {
	case c == '(':
		r.pos++
		l := &SExpr{Kind: SList}
		for {
			r.skip()
			if r.pos >= len(r.in) {
				return nil, fmt.Errorf("smt: unbalanced parentheses")
			}
			if r.in[r.pos] == ')' {
				r.pos++
				return l, nil
			}
			e, err := r.read()
			if err != nil {
				return nil, err
			}
			l.List = append(l.List, e)
		}
	case c == ')':
		return nil, fmt.Errorf("smt: unexpected ')' at %d", r.pos)
	case c == '"':
		return r.readString()
	case c == '|':
		var sb strings.Builder
		r.pos++
		for {
			if r.pos >= len(r.in) {
				return nil, fmt.Errorf("smt: unterminated quoted symbol")
			}
			ch := r.in[r.pos]
			if ch == '\\' && r.pos+1 < len(r.in) && (r.in[r.pos+1] == '|' || r.in[r.pos+1] == '\\') {
				sb.WriteByte(r.in[r.pos+1])
				r.pos += 2
				continue
			}
			if ch == '|' {
				r.pos++
				return &SExpr{Kind: SSymbol, Atom: sb.String()}, nil
			}
			sb.WriteByte(ch)
			r.pos++
		}
	case c == '#' && r.pos+1 < len(r.in) && (r.in[r.pos+1] == 'b' || r.in[r.pos+1] == 'x'):
		kind := SBinary
		if r.in[r.pos+1] == 'x' {
			kind = SHex
		}
		r.pos += 2
		start := r.pos
		for r.pos < len(r.in) && isAtomChar(r.in[r.pos]) {
			r.pos++
		}
		return &SExpr{Kind: kind, Atom: r.in[start:r.pos]}, nil
	default:
		start := r.pos
		for r.pos < len(r.in) && isAtomChar(r.in[r.pos]) {
			r.pos++
		}
		if start == r.pos {
			return nil, fmt.Errorf("smt: unexpected character %q at %d", c, r.pos)
		}
		atom := r.in[start:r.pos]
		switch {
		case atom[0] == ':':
			return &SExpr{Kind: SKeyword, Atom: atom}, nil
		case isNumeral(atom):
			return &SExpr{Kind: SNumeral, Atom: atom}, nil
		case isDecimal(atom):
			return &SExpr{Kind: SDecimal, Atom: atom}, nil
		}
		return &SExpr{Kind: SSymbol, Atom: atom}, nil
	}
}

func (r *sreader) readString() (*SExpr, error) {
	r.pos++
	var raw strings.Builder
	for {
		if r.pos >= len(r.in) {
			return nil, fmt.Errorf("smt: unterminated string")
		}
		ch := r.in[r.pos]
		if ch == '"' {
			if r.pos+1 < len(r.in) && r.in[r.pos+1] == '"' {
				raw.WriteByte('"')
				r.pos += 2
				continue
			}
			r.pos++
			break
		}
		raw.WriteByte(ch)
		r.pos++
	}
	return &SExpr{Kind: SString, Runes: decodeStringEscapes(raw.String())}, nil
}

// decodeStringEscapes decodes the \u{...} and \uXXXX escapes of SMT-LIB2 string literals.
func decodeStringEscapes(s string) []rune {
	var out []rune
	in := []rune(s)
	for i := 0; i < len(in); {
		if in[i] == '\\' && i+1 < len(in) && in[i+1] == 'u' {
			if i+2 < len(in) && in[i+2] == '{' {
				end := i + 3
				for end < len(in) && in[end] != '}' {
					end++
				}
				if end < len(in) {
					if v, err := strconv.ParseUint(string(in[i+3:end]), 16, 32); err == nil {
						out = append(out, rune(v))
						i = end + 1
						continue
					}
				}
			} else if i+6 <= len(in) {
				if v, err := strconv.ParseUint(string(in[i+2:i+6]), 16, 32); err == nil {
					out = append(out, rune(v))
					i += 6
					continue
				}
			}
		}
		out = append(out, in[i])
		i++
	}
	return out
}

func isAtomChar(c byte) bool {
	switch c {
	case '(', ')', ' ', '\t', '\n', '\r', '"', ';', '|':
		return false
	}
	return true
}

func isNumeral(s string) bool {
	for _, c := range s {
		if c < '0' || c > '9' {
			return false
		}
	}
	return s != ""
}

func isDecimal(s string) bool {
	parts := strings.SplitN(s, ".", 2)
	return len(parts) == 2 && isNumeral(parts[0]) && isNumeral(parts[1])
}
