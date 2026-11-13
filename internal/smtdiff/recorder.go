package smtdiff

import (
	"fmt"
	"strings"
	"sync"

	"github.com/swist/cel-go-verifier/smt"
)

// Recorder writes solver interactions in the javaref transcript format.
type Recorder struct {
	mu      sync.Mutex
	sb      strings.Builder
	queries int
	method  string
}

// Factory returns a recorder factory that appends to r, for verifier.Recorder.
func (r *Recorder) Factory() func() smt.Recorder {
	return func() smt.Recorder { return &queryRecorder{r: r} }
}

// String returns the transcript.
func (r *Recorder) String() string {
	r.mu.Lock()
	defer r.mu.Unlock()
	return r.sb.String()
}

// Reset clears the transcript.
func (r *Recorder) Reset() {
	r.mu.Lock()
	defer r.mu.Unlock()
	r.sb.Reset()
	r.queries = 0
}

type queryRecorder struct{ r *Recorder }

func (q *queryRecorder) write(s string) {
	q.r.mu.Lock()
	q.r.sb.WriteString(s)
	q.r.mu.Unlock()
}

func (q *queryRecorder) NewSolver() {}

// Method starts the query section; the verifier calls it right after NewSolver.
func (q *queryRecorder) Method(m string) {
	q.r.mu.Lock()
	q.r.queries++
	fmt.Fprintf(&q.r.sb, ";; query %d %s\n", q.r.queries, m)
	q.r.mu.Unlock()
}

func (q *queryRecorder) Push() { q.write("(push)\n") }
func (q *queryRecorder) Pop()  { q.write("(pop)\n") }
func (q *queryRecorder) Assert(ts ...*smt.Term) {
	var sb strings.Builder
	for _, t := range ts {
		sb.WriteString("(assert " + strings.ReplaceAll(smt.Print(t), "\n", " ") + ")\n")
	}
	q.write(sb.String())
}
func (q *queryRecorder) Check(s smt.Status) { q.write("(check-sat) ; " + s.String() + "\n") }
