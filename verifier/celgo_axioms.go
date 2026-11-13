package verifier

import (
	"cel.dev/cel-go/common/types"

	"github.com/swist/cel-go-verifier/smt"
)

// Overloads cel-go's standard library has and cel-java's doesn't. They extend
// the cel-java declarations at the end, so calls that can't reach them
// translate exactly as in cel-java.
func init() {
	d := standardDecls["int"]
	d.Overloads = append(d.Overloads, OverloadDecl{ID: "duration_to_int64", Params: []*types.Type{types.DurationType}, Result: types.IntType})
	standardDecls["int"] = d
}

func celGoAxioms(int *FunctionAxiom) *FunctionAxiom {
	// int(duration) is the duration in nanoseconds, always within int64.
	return int.Unary("duration_to_int64", func(_ *smt.Context, ts *TypeSystem, _ func(*smt.Term), arg *smt.Term) (*smt.Term, bool) {
		return ts.WrapInt(ts.GetDuration(arg)), true
	}, false)
}
