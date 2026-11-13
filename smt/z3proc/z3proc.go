// Package z3proc is an smt.Backend that drives the z3 binary over its
// SMT-LIB2 text interface. It needs no cgo: point it at a z3 executable with
// the Z3_PATH environment variable or put z3 on the PATH.
package z3proc

import (
	"bufio"
	"context"
	"fmt"
	"io"
	"os"
	"os/exec"
	"strings"
	"sync"
	"time"

	"github.com/swist/cel-go-verifier/smt"
)

// Backend runs z3 processes: one per context for simplification, and one per solver.
type Backend struct {
	// Path of the z3 executable.
	Path string

	mu          sync.Mutex
	simplifiers map[*smt.Context]*process
}

// New returns a backend using the z3 executable named by $Z3_PATH, or z3 on the PATH.
func New() *Backend {
	path := os.Getenv("Z3_PATH")
	if path == "" {
		path = "z3"
	}
	return &Backend{Path: path, simplifiers: map[*smt.Context]*process{}}
}

// Available reports whether the z3 executable can be found.
func (b *Backend) Available() bool {
	_, err := exec.LookPath(b.Path)
	return err == nil
}

// Simplify implements smt.Backend.
func (b *Backend) Simplify(c *smt.Context, t *smt.Term) *smt.Term {
	b.mu.Lock()
	p := b.simplifiers[c]
	if p == nil {
		var err error
		p, err = b.start(c)
		if err != nil {
			b.mu.Unlock()
			panic(fmt.Sprintf("z3proc: %v", err))
		}
		b.simplifiers[c] = p
	}
	b.mu.Unlock()
	out, err := p.query("(simplify " + p.term(t) + ")")
	if err != nil {
		panic(fmt.Sprintf("z3proc: simplify: %v", err))
	}
	r, err := c.ParseTerm(out)
	if err != nil {
		panic(fmt.Sprintf("z3proc: parsing simplified term: %v", err))
	}
	return r
}

// Close implements smt.Backend.
func (b *Backend) Close(c *smt.Context) {
	b.mu.Lock()
	p := b.simplifiers[c]
	delete(b.simplifiers, c)
	b.mu.Unlock()
	if p != nil {
		p.close()
	}
}

// NewSolver implements smt.Backend.
func (b *Backend) NewSolver(c *smt.Context, timeout time.Duration) (smt.Solver, error) {
	p, err := b.start(c)
	if err != nil {
		return nil, err
	}
	s := &solver{p: p, timeout: timeout}
	if timeout > 0 {
		p.send(fmt.Sprintf("(set-option :timeout %d)", timeout.Milliseconds()))
	}
	return s, nil
}

// process is a running z3 with the declarations it has seen.
type process struct {
	c        *smt.Context
	cmd      *exec.Cmd
	stdin    io.WriteCloser
	stdout   *bufio.Reader
	pending  strings.Builder
	sorts    map[*smt.Sort]bool
	decls    map[*smt.FuncDecl]bool
	sources  map[*smt.Term]*smt.Term
	cancel   context.CancelFunc
	closed   bool
	stderr   strings.Builder
	stderrMu sync.Mutex
}

const marker = "<<z3proc-done>>"

func (b *Backend) start(c *smt.Context) (*process, error) {
	ctx, cancel := context.WithCancel(context.Background())
	cmd := exec.CommandContext(ctx, b.Path, "-in", "-smt2")
	stdin, err := cmd.StdinPipe()
	if err != nil {
		cancel()
		return nil, err
	}
	stdout, err := cmd.StdoutPipe()
	if err != nil {
		cancel()
		return nil, err
	}
	p := &process{
		c: c, cmd: cmd, stdin: stdin, stdout: bufio.NewReaderSize(stdout, 1<<20),
		sorts: map[*smt.Sort]bool{}, decls: map[*smt.FuncDecl]bool{}, sources: map[*smt.Term]*smt.Term{},
		cancel: cancel,
	}
	cmd.Stderr = writerFunc(func(b []byte) (int, error) {
		p.stderrMu.Lock()
		p.stderr.Write(b)
		p.stderrMu.Unlock()
		return len(b), nil
	})
	if err := cmd.Start(); err != nil {
		cancel()
		return nil, fmt.Errorf("starting %s: %w", b.Path, err)
	}
	p.send("(set-option :print-success false)")
	p.send("(set-option :model true)")
	return p, nil
}

type writerFunc func([]byte) (int, error)

func (f writerFunc) Write(b []byte) (int, error) { return f(b) }

func (p *process) send(cmd string) {
	p.pending.WriteString(cmd)
	p.pending.WriteByte('\n')
}

// query sends the pending commands and cmd, and returns cmd's output.
func (p *process) query(cmd string) (string, error) {
	if p.closed {
		return "", fmt.Errorf("z3 process is closed")
	}
	p.send(cmd)
	p.send(`(echo "` + marker + `")`)
	if _, err := io.WriteString(p.stdin, p.pending.String()); err != nil {
		return "", p.wrapErr(err)
	}
	p.pending.Reset()
	var out strings.Builder
	for {
		line, err := p.stdout.ReadString('\n')
		if err != nil {
			return "", p.wrapErr(err)
		}
		if strings.TrimRight(line, "\r\n") == marker {
			break
		}
		out.WriteString(line)
	}
	s := strings.TrimSpace(out.String())
	if strings.HasPrefix(s, "(error") {
		return "", fmt.Errorf("z3: %s", s)
	}
	if i := strings.Index(s, "\n(error"); i >= 0 {
		return "", fmt.Errorf("z3: %s", s[i+1:])
	}
	return s, nil
}

func (p *process) wrapErr(err error) error {
	p.stderrMu.Lock()
	defer p.stderrMu.Unlock()
	if p.stderr.Len() > 0 {
		return fmt.Errorf("%w: %s", err, p.stderr.String())
	}
	return err
}

func (p *process) close() {
	if p.closed {
		return
	}
	p.closed = true
	_, _ = io.WriteString(p.stdin, p.pending.String()+"(exit)\n")
	_ = p.stdin.Close()
	done := make(chan struct{})
	go func() { _ = p.cmd.Wait(); close(done) }()
	select {
	case <-done:
	case <-time.After(2 * time.Second):
		p.cancel()
		<-done
	}
	p.cancel()
}

// term declares what t needs and renders it, replacing model values with terms that evaluate to them.
func (p *process) term(t *smt.Term) string {
	if len(p.sources) > 0 {
		t = p.substituteModelValues(t)
	}
	p.declare(t)
	return smt.Print(t)
}

func (p *process) substituteModelValues(t *smt.Term) *smt.Term {
	var from, to []*smt.Term
	seen := map[*smt.Term]bool{}
	var walk func(*smt.Term)
	walk = func(t *smt.Term) {
		if seen[t] {
			return
		}
		seen[t] = true
		if t.Op == smt.OpModelValue {
			if src, ok := p.sources[t]; ok {
				from = append(from, t)
				to = append(to, src)
			}
			return
		}
		for _, a := range t.Args {
			walk(a)
		}
	}
	walk(t)
	if len(from) == 0 {
		return t
	}
	return p.c.Substitute(t, from, to)
}

func (p *process) declare(t *smt.Term) {
	var sorts []*smt.Sort
	var decls []*smt.FuncDecl
	seenT := map[*smt.Term]bool{}
	var visitSort func(*smt.Sort)
	visitSort = func(s *smt.Sort) {
		switch s.Kind {
		case smt.KindSeq, smt.KindArray:
			for _, ps := range s.Params {
				visitSort(ps)
			}
		case smt.KindUninterpreted, smt.KindDatatype:
			if !p.sorts[s] {
				sorts = append(sorts, s)
			}
		}
	}
	var walk func(*smt.Term)
	walk = func(t *smt.Term) {
		if seenT[t] {
			return
		}
		seenT[t] = true
		visitSort(t.Sort)
		if (t.Op == smt.OpApp || t.Op == smt.OpAsArray) && t.Decl.Kind == smt.DeclUninterpreted && !p.decls[t.Decl] {
			decls = append(decls, t.Decl)
			for _, s := range t.Decl.Domain {
				visitSort(s)
			}
		}
		for _, v := range t.Vars {
			visitSort(v.Sort)
		}
		for _, a := range t.Args {
			walk(a)
		}
	}
	walk(t)
	if len(sorts) > 0 {
		// Declare in creation order, which respects dependencies.
		need := map[*smt.Sort]bool{}
		for _, s := range sorts {
			need[s] = true
			if s.Datatype != nil {
				for _, k := range s.Datatype.Constructors {
					for _, fs := range k.FieldSorts {
						markSorts(fs, need)
					}
				}
			}
		}
		for _, s := range p.c.Sorts() {
			if need[s] && !p.sorts[s] {
				p.sorts[s] = true
				p.send(smt.DeclareSort(s))
			}
		}
	}
	for _, d := range decls {
		if !p.decls[d] {
			p.decls[d] = true
			p.send(smt.DeclareFun(d))
		}
	}
}

func markSorts(s *smt.Sort, need map[*smt.Sort]bool) {
	switch s.Kind {
	case smt.KindSeq, smt.KindArray:
		for _, ps := range s.Params {
			markSorts(ps, need)
		}
	case smt.KindUninterpreted, smt.KindDatatype:
		need[s] = true
	}
}

type solver struct {
	p       *process
	timeout time.Duration
	reason  string
}

func (s *solver) Push() { s.p.send("(push 1)"); s.p.sources = map[*smt.Term]*smt.Term{} }
func (s *solver) Pop()  { s.p.send("(pop 1)"); s.p.sources = map[*smt.Term]*smt.Term{} }

func (s *solver) Assert(ts ...*smt.Term) {
	s.p.sources = map[*smt.Term]*smt.Term{}
	for _, t := range ts {
		s.p.send("(assert " + s.p.term(t) + ")")
	}
}

func (s *solver) Check() (smt.Status, error) {
	s.p.sources = map[*smt.Term]*smt.Term{}
	var timer *time.Timer
	if s.timeout > 0 {
		// Z3 enforces the timeout itself; this only guards against a hung process.
		timer = time.AfterFunc(s.timeout*4+10*time.Second, s.p.cancel)
	}
	out, err := s.p.query("(check-sat)")
	if timer != nil {
		timer.Stop()
	}
	if err != nil {
		return smt.Unknown, err
	}
	switch out {
	case "sat":
		s.reason = ""
		return smt.Sat, nil
	case "unsat":
		s.reason = ""
		return smt.Unsat, nil
	case "unknown":
		r, err := s.p.query("(get-info :reason-unknown)")
		if err != nil {
			return smt.Unknown, err
		}
		s.reason = parseReason(r)
		return smt.Unknown, nil
	}
	return smt.Unknown, fmt.Errorf("z3: unexpected check-sat output %q", out)
}

func parseReason(r string) string {
	e, err := smt.ParseSExpr(r)
	if err != nil || e.Kind != smt.SList || len(e.List) != 2 {
		return r
	}
	if e.List[1].Kind == smt.SString {
		return string(e.List[1].Runes)
	}
	return e.List[1].String()
}

func (s *solver) ReasonUnknown() string { return s.reason }

func (s *solver) Close() { s.p.close() }

func (s *solver) Model() smt.Model { return &model{s: s} }

type model struct{ s *solver }

func (m *model) Eval(t *smt.Term, completion bool) (*smt.Term, error) {
	p := m.s.p
	cmd := "(eval " + p.term(t)
	if completion {
		cmd += " :completion true"
	}
	out, err := p.query(cmd + ")")
	if err != nil {
		return nil, err
	}
	v, err := p.c.ParseTerm(out)
	if err != nil {
		return nil, err
	}
	m.recordSources(v, t)
	return v, nil
}

// recordSources remembers, for the model values in v, terms that evaluate to them, so that
// terms built from v can be sent back to z3 (which can't parse model values).
func (m *model) recordSources(v, src *smt.Term) {
	p := m.s.p
	c := p.c
	switch {
	case v.Op == smt.OpModelValue:
		if _, ok := p.sources[v]; !ok {
			p.sources[v] = src
		}
	case v.Op == smt.OpApp && v.Decl.Kind == smt.DeclConstructor:
		for i, a := range v.Args {
			m.recordSources(a, c.MkApp(v.Decl.Cons.Accessors[i], src))
		}
	case v.Op == smt.OpSeqUnit:
		m.recordSources(v.Args[0], c.MkNth(src, c.MkInt(0)))
	case v.Op == smt.OpSeqConcat:
		var units []*smt.Term
		flattenConcat(v, &units)
		for i, u := range units {
			if u.Op == smt.OpSeqUnit {
				m.recordSources(u.Args[0], c.MkNth(src, c.MkInt(int64(i))))
			} else {
				return
			}
		}
	case v.Op == smt.OpStore:
		if !hasModelValue(v.Args[1]) {
			m.recordSources(v.Args[2], c.MkSelect(src, v.Args[1]))
		}
	}
}

func flattenConcat(t *smt.Term, out *[]*smt.Term) {
	if t.Op == smt.OpSeqConcat {
		for _, a := range t.Args {
			flattenConcat(a, out)
		}
		return
	}
	*out = append(*out, t)
}

func hasModelValue(t *smt.Term) bool {
	if t.Op == smt.OpModelValue {
		return true
	}
	for _, a := range t.Args {
		if hasModelValue(a) {
			return true
		}
	}
	return false
}
