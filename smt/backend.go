package smt

import "time"

// Status is the outcome of a satisfiability check.
type Status int

// Statuses.
const (
	Unknown Status = iota
	Sat
	Unsat
)

func (s Status) String() string {
	switch s {
	case Sat:
		return "SATISFIABLE"
	case Unsat:
		return "UNSATISFIABLE"
	default:
		return "UNKNOWN"
	}
}

// Backend provides the solver services the term layer can't: simplification
// and satisfiability checking.
type Backend interface {
	// Simplify simplifies t with Z3's default simplifier.
	Simplify(c *Context, t *Term) *Term
	// NewSolver creates a solver for terms of c.
	NewSolver(c *Context, timeout time.Duration) (Solver, error)
	// Close releases the resources held by the backend for c.
	Close(c *Context)
}

// Solver mirrors com.microsoft.z3.Solver.
type Solver interface {
	Push()
	Pop()
	Assert(ts ...*Term)
	Check() (Status, error)
	// Model returns the model of the last satisfiable check. It is valid until the next
	// call that changes the solver's state.
	Model() Model
	// ReasonUnknown explains an unknown status, e.g. "timeout" or "canceled".
	ReasonUnknown() string
	Close()
}

// Model evaluates terms in a model.
type Model interface {
	// Eval evaluates t. With completion, unconstrained symbols are given default values.
	Eval(t *Term, completion bool) (*Term, error)
}

// Recorder observes solver interactions, e.g. to write SMT-LIB2 transcripts.
type Recorder interface {
	NewSolver()
	Push()
	Pop()
	Assert(ts ...*Term)
	Check(Status)
}

// RecordingSolver wraps a solver to report its interactions to a recorder.
type RecordingSolver struct {
	Solver
	Rec Recorder
}

// Push implements Solver.
func (r *RecordingSolver) Push() { r.Rec.Push(); r.Solver.Push() }

// Pop implements Solver.
func (r *RecordingSolver) Pop() { r.Rec.Pop(); r.Solver.Pop() }

// Assert implements Solver.
func (r *RecordingSolver) Assert(ts ...*Term) { r.Rec.Assert(ts...); r.Solver.Assert(ts...) }

// Check implements Solver.
func (r *RecordingSolver) Check() (Status, error) {
	st, err := r.Solver.Check()
	if err == nil {
		r.Rec.Check(st)
	}
	return st, err
}
