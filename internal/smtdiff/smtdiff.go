// Package smtdiff compares SMT-LIB2 solver transcripts structurally: let
// bindings are expanded, symbol quoting and numeral, string and floating point
// literal spellings are normalized, and Z3's str.* aliases of seq.* operations
// are identified. Terms are hash-consed, so shared subterms stay cheap.
package smtdiff

import (
	"bufio"
	"fmt"
	"math/big"
	"strconv"
	"strings"

	"github.com/swist/cel-go-verifier/smt"
)

// Command is one solver interaction.
type Command struct {
	// Kind is "push", "pop", "assert" or "check".
	Kind string
	// Term is the canonical id of an asserted term.
	Term int
	// Status is the result of a check.
	Status string
}

// Query is the transcript of one solver.
type Query struct {
	Method   string
	Commands []Command
}

// Canonicalizer interns canonical terms. Transcripts compared with each other
// must be parsed by the same Canonicalizer.
type Canonicalizer struct {
	ids   map[string]int
	nodes []string
}

// New returns an empty canonicalizer.
func New() *Canonicalizer { return &Canonicalizer{ids: map[string]int{}} }

func (c *Canonicalizer) intern(key string) int {
	if id, ok := c.ids[key]; ok {
		return id
	}
	id := len(c.nodes)
	c.ids[key] = id
	c.nodes = append(c.nodes, key)
	return id
}

// Render prints a canonical term, truncated to about max bytes.
func (c *Canonicalizer) Render(id, max int) string {
	var sb strings.Builder
	c.render(&sb, id, max)
	return sb.String()
}

func (c *Canonicalizer) render(sb *strings.Builder, id, max int) {
	if sb.Len() > max {
		sb.WriteString("…")
		return
	}
	key := c.nodes[id]
	head, args, ok := splitNode(key)
	if !ok {
		sb.WriteString(key)
		return
	}
	sb.WriteString("(" + head)
	for _, a := range args {
		sb.WriteByte(' ')
		c.render(sb, a, max)
	}
	sb.WriteString(")")
}

func splitNode(key string) (string, []int, bool) {
	if !strings.HasPrefix(key, "(") {
		return "", nil, false
	}
	parts := strings.Split(key[1:len(key)-1], "\x00")
	var args []int
	for _, p := range parts[1:] {
		n, _ := strconv.Atoi(p)
		args = append(args, n)
	}
	return parts[0], args, true
}

// Parse reads a transcript in the format written by the javaref SmtDump hook.
func (c *Canonicalizer) Parse(transcript string) ([]Query, error) {
	var out []Query
	sc := bufio.NewScanner(strings.NewReader(transcript))
	sc.Buffer(make([]byte, 1<<20), 1<<30)
	for sc.Scan() {
		line := sc.Text()
		switch {
		case strings.HasPrefix(line, ";; query "):
			f := strings.Fields(line)
			out = append(out, Query{Method: f[len(f)-1]})
		case line == "(push)":
			out[len(out)-1].Commands = append(out[len(out)-1].Commands, Command{Kind: "push"})
		case line == "(pop)":
			out[len(out)-1].Commands = append(out[len(out)-1].Commands, Command{Kind: "pop"})
		case strings.HasPrefix(line, "(check-sat)"):
			st := strings.TrimSpace(strings.TrimPrefix(line, "(check-sat) ;"))
			out[len(out)-1].Commands = append(out[len(out)-1].Commands, Command{Kind: "check", Status: st})
		case strings.HasPrefix(line, "(assert "):
			e, err := smt.ParseSExpr(line)
			if err != nil {
				return nil, err
			}
			id, err := c.Canon(e.List[1])
			if err != nil {
				return nil, err
			}
			out[len(out)-1].Commands = append(out[len(out)-1].Commands, Command{Kind: "assert", Term: id})
		case strings.TrimSpace(line) == "":
		default:
			return nil, fmt.Errorf("smtdiff: unexpected line %q", truncate(line, 100))
		}
	}
	return out, sc.Err()
}

func truncate(s string, n int) string {
	if len(s) > n {
		return s[:n] + "…"
	}
	return s
}

var flatAssoc = map[string]bool{"and": true, "or": true, "+": true, "*": true, "seq.++": true}

var aliases = map[string]string{
	"str.++": "seq.++", "str.len": "seq.len", "str.contains": "seq.contains",
	"str.prefixof": "seq.prefixof", "str.suffixof": "seq.suffixof", "str.indexof": "seq.indexof",
	"str.substr": "seq.extract", "str.at": "seq.at", "str.replace": "seq.replace",
	"str.last_indexof": "seq.last_indexof", "str.to.int": "str.to_int", "int.to.str": "str.from_int",
	"bv2int": "ubv_to_int",
}

// Canon interns the canonical form of a term.
func (c *Canonicalizer) Canon(e *smt.SExpr) (int, error) {
	return c.canon(e, nil)
}

type scope struct {
	names  map[string]int
	parent *scope
}

func (s *scope) lookup(n string) (int, bool) {
	for cur := s; cur != nil; cur = cur.parent {
		if id, ok := cur.names[n]; ok {
			return id, true
		}
	}
	return 0, false
}

func (c *Canonicalizer) canon(e *smt.SExpr, sc *scope) (int, error) {
	switch e.Kind {
	case smt.SSymbol:
		if id, ok := sc.lookup(e.Atom); ok {
			return id, nil
		}
		return c.intern("sym:" + e.Atom), nil
	case smt.SNumeral:
		return c.intern("int:" + e.Atom), nil
	case smt.SDecimal:
		r, _ := new(big.Rat).SetString(e.Atom)
		return c.intern("real:" + r.RatString()), nil
	case smt.SString:
		return c.intern("str:" + smt.QuoteString(e.Runes)), nil
	case smt.SBinary:
		v, _ := new(big.Int).SetString(e.Atom, 2)
		return c.intern(fmt.Sprintf("bv%d:%s", len(e.Atom), v)), nil
	case smt.SHex:
		v, _ := new(big.Int).SetString(e.Atom, 16)
		return c.intern(fmt.Sprintf("bv%d:%s", 4*len(e.Atom), v)), nil
	case smt.SKeyword:
		return c.intern(e.Atom), nil
	}
	l := e.List
	if len(l) == 0 {
		return c.intern("()"), nil
	}
	if l[0].IsSymbol("let") {
		inner := &scope{names: map[string]int{}, parent: sc}
		for _, b := range l[1].List {
			id, err := c.canon(b.List[1], sc)
			if err != nil {
				return 0, err
			}
			inner.names[b.List[0].Atom] = id
		}
		return c.canon(l[2], inner)
	}
	// Literals spelled in several ways.
	if l[0].IsSymbol("-") && len(l) == 2 && l[1].Kind == smt.SNumeral {
		return c.intern("int:-" + l[1].Atom), nil
	}
	if l[0].IsSymbol("_") && len(l) == 4 {
		switch l[1].Atom {
		case "+zero", "-zero", "+oo", "-oo", "NaN":
			return c.intern(fmt.Sprintf("fp%s,%s:%s", l[2].Atom, l[3].Atom, l[1].Atom)), nil
		}
	}
	if l[0].IsSymbol("fp") && len(l) == 4 && isBits(l[1]) && isBits(l[2]) && isBits(l[3]) {
		return c.intern(fmt.Sprintf("fp%d,%d:%s%s%s", bitWidth(l[2]), bitWidth(l[3])+1, bitString(l[1]), bitString(l[2]), bitString(l[3]))), nil
	}
	var head string
	start := 1
	switch {
	case l[0].Kind == smt.SSymbol:
		head = l[0].Atom
		if a, ok := aliases[head]; ok {
			head = a
		}
	default:
		// Indexed or qualified heads keep their spelling, minus whitespace.
		head = l[0].String()
	}
	if l[0].IsSymbol("as") || l[0].IsSymbol("_") {
		return c.intern(e.String()), nil
	}
	args := make([]string, 0, len(l))
	args = append(args, head)
	for _, a := range l[start:] {
		id, err := c.canon(a, sc)
		if err != nil {
			return 0, err
		}
		// Z3's printer flattens nested applications of associative operators (pp.flat_assoc).
		if flatAssoc[head] {
			if h, sub, ok := splitNode(c.nodes[id]); ok && h == head {
				for _, x := range sub {
					args = append(args, strconv.Itoa(x))
				}
				continue
			}
		}
		args = append(args, strconv.Itoa(id))
	}
	return c.intern("(" + strings.Join(args, "\x00") + ")"), nil
}

func isBits(e *smt.SExpr) bool { return e.Kind == smt.SBinary || e.Kind == smt.SHex }

func bitWidth(e *smt.SExpr) int {
	if e.Kind == smt.SBinary {
		return len(e.Atom)
	}
	return 4 * len(e.Atom)
}

func bitString(e *smt.SExpr) string {
	if e.Kind == smt.SBinary {
		return e.Atom
	}
	v, _ := new(big.Int).SetString(e.Atom, 16)
	s := v.Text(2)
	return strings.Repeat("0", 4*len(e.Atom)-len(s)) + s
}

// FirstDiff returns the first differing assertions of two transcripts, or ok=false.
func (c *Canonicalizer) FirstDiff(want, got []Query) (w, g int, ok bool) {
	for i := range want {
		if i >= len(got) {
			return 0, 0, false
		}
		for j := range want[i].Commands {
			if j >= len(got[i].Commands) {
				return 0, 0, false
			}
			wc, gc := want[i].Commands[j], got[i].Commands[j]
			if wc.Kind == "assert" && gc.Kind == "assert" && wc.Term != gc.Term {
				return wc.Term, gc.Term, true
			}
		}
	}
	return 0, 0, false
}

// RenderPretty prints a canonical term with one subterm per line, for diffing.
func (c *Canonicalizer) RenderPretty(id int) string {
	var sb strings.Builder
	var walk func(id, depth int)
	walk = func(id, depth int) {
		if sb.Len() > 1<<22 {
			return
		}
		head, args, ok := splitNode(c.nodes[id])
		sb.WriteString(strings.Repeat(" ", depth))
		if !ok {
			sb.WriteString(c.nodes[id] + "\n")
			return
		}
		sb.WriteString("(" + head + "\n")
		for _, a := range args {
			walk(a, depth+1)
		}
	}
	walk(id, 0)
	return sb.String()
}

// Diff compares two parsed transcripts and describes the first difference.
func (c *Canonicalizer) Diff(want, got []Query) string {
	if len(want) != len(got) {
		return fmt.Sprintf("query count: want %d, got %d", len(want), len(got))
	}
	for i := range want {
		w, g := want[i], got[i]
		if w.Method != g.Method {
			return fmt.Sprintf("query %d: method: want %s, got %s", i+1, w.Method, g.Method)
		}
		n := len(w.Commands)
		if len(g.Commands) < n {
			n = len(g.Commands)
		}
		for j := 0; j < n; j++ {
			wc, gc := w.Commands[j], g.Commands[j]
			if wc.Kind != gc.Kind {
				return fmt.Sprintf("query %d command %d: want %s, got %s", i+1, j, wc.Kind, gc.Kind)
			}
			if wc.Kind == "assert" && wc.Term != gc.Term {
				return fmt.Sprintf("query %d command %d: assertion differs:\n%s", i+1, j, c.ExplainDiff(wc.Term, gc.Term))
			}
			if wc.Kind == "check" && wc.Status != gc.Status {
				return fmt.Sprintf("query %d command %d: check status: want %s, got %s", i+1, j, wc.Status, gc.Status)
			}
		}
		if len(w.Commands) != len(g.Commands) {
			return fmt.Sprintf("query %d: command count: want %d, got %d", i+1, len(w.Commands), len(g.Commands))
		}
	}
	return ""
}

// ExplainDiff descends to the first differing subterms of two terms.
func (c *Canonicalizer) ExplainDiff(want, got int) string {
	path := ""
	for {
		wh, wa, wok := splitNode(c.nodes[want])
		gh, ga, gok := splitNode(c.nodes[got])
		if !wok || !gok || wh != gh || len(wa) != len(ga) {
			return fmt.Sprintf("at %s\n  want: %s\n  got:  %s", path, c.Render(want, 600), c.Render(got, 600))
		}
		moved := false
		for i := range wa {
			if wa[i] != ga[i] {
				path += fmt.Sprintf("/%s[%d]", wh, i)
				want, got = wa[i], ga[i]
				moved = true
				break
			}
		}
		if !moved {
			return "identical"
		}
	}
}
