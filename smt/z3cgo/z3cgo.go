//go:build z3cgo

package z3cgo

/*
#cgo LDFLAGS: -lz3
#include <stdlib.h>
#include <z3.h>

static void noop_error_handler(Z3_context c, Z3_error_code e) {}
static void set_noop_handler(Z3_context c) { Z3_set_error_handler(c, noop_error_handler); }
*/
import "C"

import (
	"fmt"
	"math"
	"strconv"
	"strings"
	"sync"
	"time"
	"unsafe"

	"github.com/swist/cel-go-verifier/smt"
)

// Enabled reports whether the package was built with the z3cgo tag.
const Enabled = true

// Backend links libz3. Each smt.Context gets its own Z3 context, in which
// every term is created as soon as the smt.Context creates it, exactly as the
// Z3 Java API does. That makes Z3's simplifier, which orders arguments by
// creation, behave as it does for cel-java.
type Backend struct {
	mu   sync.Mutex
	ctxs map[*smt.Context]*zctx
}

// New returns a backend.
func New() *Backend { return &Backend{ctxs: map[*smt.Context]*zctx{}} }

type zctx struct {
	c      *smt.Context
	z      C.Z3_context
	sorts  map[*smt.Sort]C.Z3_sort
	decls  map[*smt.FuncDecl]C.Z3_func_decl
	terms  map[*smt.Term]C.Z3_ast
	values map[string]C.Z3_ast       // model values by name
	ops    map[string]C.Z3_func_decl // builtin declarations seen in Z3's output, by name and arity
	rms    map[smt.RoundingMode]C.Z3_ast
}

// Observe implements the smt.Context observer hook.
func (b *Backend) Observe(c *smt.Context) smt.Observer {
	cfg := C.Z3_mk_config()
	k, v := C.CString("model"), C.CString("true")
	C.Z3_set_param_value(cfg, k, v)
	C.free(unsafe.Pointer(k))
	C.free(unsafe.Pointer(v))
	z := C.Z3_mk_context_rc(cfg)
	C.Z3_del_config(cfg)
	C.set_noop_handler(z)
	zc := &zctx{
		c: c, z: z, sorts: map[*smt.Sort]C.Z3_sort{}, decls: map[*smt.FuncDecl]C.Z3_func_decl{},
		terms: map[*smt.Term]C.Z3_ast{}, values: map[string]C.Z3_ast{}, ops: map[string]C.Z3_func_decl{},
		rms: map[smt.RoundingMode]C.Z3_ast{},
	}
	b.mu.Lock()
	b.ctxs[c] = zc
	b.mu.Unlock()
	return zc
}

func (b *Backend) ctx(c *smt.Context) *zctx {
	b.mu.Lock()
	defer b.mu.Unlock()
	zc := b.ctxs[c]
	if zc == nil {
		panic("z3cgo: context was not created with this backend")
	}
	return zc
}

// Close implements smt.Backend.
func (b *Backend) Close(c *smt.Context) {
	b.mu.Lock()
	zc := b.ctxs[c]
	delete(b.ctxs, c)
	b.mu.Unlock()
	if zc != nil {
		C.Z3_del_context(zc.z)
	}
}

func (zc *zctx) check(what string) {
	if code := C.Z3_get_error_code(zc.z); code != C.Z3_OK {
		msg := C.GoString(C.Z3_get_error_msg(zc.z, code))
		panic(fmt.Sprintf("z3cgo: %s: %s", what, msg))
	}
}

func (zc *zctx) sym(name string) C.Z3_symbol {
	cs := C.CString(name)
	defer C.free(unsafe.Pointer(cs))
	return C.Z3_mk_string_symbol(zc.z, cs)
}

func (zc *zctx) keepSort(s C.Z3_sort) C.Z3_sort {
	C.Z3_inc_ref(zc.z, C.Z3_sort_to_ast(zc.z, s))
	return s
}

func (zc *zctx) keepDecl(d C.Z3_func_decl) C.Z3_func_decl {
	C.Z3_inc_ref(zc.z, C.Z3_func_decl_to_ast(zc.z, d))
	return d
}

// OnSort implements smt.Observer.
func (zc *zctx) OnSort(s *smt.Sort) {
	if _, ok := zc.sorts[s]; ok {
		return
	}
	z := zc.z
	var r C.Z3_sort
	switch s.Kind {
	case smt.KindBool:
		r = C.Z3_mk_bool_sort(z)
	case smt.KindInt:
		r = C.Z3_mk_int_sort(z)
	case smt.KindReal:
		r = C.Z3_mk_real_sort(z)
	case smt.KindString:
		r = C.Z3_mk_string_sort(z)
	case smt.KindChar:
		r = C.Z3_mk_char_sort(z)
	case smt.KindSeq:
		r = C.Z3_mk_seq_sort(z, zc.sort(s.Elem()))
	case smt.KindArray:
		r = C.Z3_mk_array_sort(z, zc.sort(s.Domain()), zc.sort(s.Range()))
	case smt.KindFP:
		r = C.Z3_mk_fpa_sort(z, C.uint(s.EBits), C.uint(s.SBits))
	case smt.KindBV:
		r = C.Z3_mk_bv_sort(z, C.uint(s.Size))
	case smt.KindRoundingMode:
		r = C.Z3_mk_fpa_rounding_mode_sort(z)
	case smt.KindUninterpreted:
		r = C.Z3_mk_uninterpreted_sort(z, zc.sym(s.Name))
	case smt.KindDatatype:
		r = zc.mkDatatype(s)
	}
	zc.check("sort " + s.String())
	zc.sorts[s] = zc.keepSort(r)
}

func (zc *zctx) sort(s *smt.Sort) C.Z3_sort {
	if r, ok := zc.sorts[s]; ok {
		return r
	}
	zc.OnSort(s)
	return zc.sorts[s]
}

func (zc *zctx) mkDatatype(s *smt.Sort) C.Z3_sort {
	z := zc.z
	dt := s.Datatype
	cons := make([]C.Z3_constructor, len(dt.Constructors))
	for i, k := range dt.Constructors {
		n := len(k.FieldNames)
		names := make([]C.Z3_symbol, n+1)
		sorts := make([]C.Z3_sort, n+1)
		refs := make([]C.uint, n+1)
		for j := range k.FieldNames {
			names[j] = zc.sym(k.FieldNames[j])
			sorts[j] = zc.sort(k.FieldSorts[j])
		}
		cons[i] = C.Z3_mk_constructor(z, zc.sym(k.Name), zc.sym(k.TesterName), C.uint(n), &names[0], &sorts[0], &refs[0])
	}
	r := C.Z3_mk_datatype(z, zc.sym(dt.Name), C.uint(len(cons)), &cons[0])
	for i, k := range dt.Constructors {
		n := len(k.FieldNames)
		var cd, td C.Z3_func_decl
		acc := make([]C.Z3_func_decl, n+1)
		C.Z3_query_constructor(z, cons[i], C.uint(n), &cd, &td, &acc[0])
		zc.decls[k.Decl] = zc.keepDecl(cd)
		zc.decls[k.Tester] = zc.keepDecl(td)
		for j := 0; j < n; j++ {
			zc.decls[k.Accessors[j]] = zc.keepDecl(acc[j])
		}
		C.Z3_del_constructor(z, cons[i])
	}
	return r
}

// OnDecl implements smt.Observer.
func (zc *zctx) OnDecl(d *smt.FuncDecl) {
	if _, ok := zc.decls[d]; ok {
		return
	}
	dom := make([]C.Z3_sort, len(d.Domain)+1)
	for i, s := range d.Domain {
		dom[i] = zc.sort(s)
	}
	r := C.Z3_mk_func_decl(zc.z, zc.sym(d.Name), C.uint(len(d.Domain)), &dom[0], zc.sort(d.Range))
	zc.check("declare " + d.Name)
	zc.decls[d] = zc.keepDecl(r)
}

func (zc *zctx) decl(d *smt.FuncDecl) C.Z3_func_decl {
	if r, ok := zc.decls[d]; ok {
		return r
	}
	if d.Kind == smt.DeclUninterpreted {
		zc.OnDecl(d)
		return zc.decls[d]
	}
	zc.sort(d.Range)
	zc.sort(d.Domain[0])
	return zc.decls[d]
}

// OnTerm implements smt.Observer.
func (zc *zctx) OnTerm(t *smt.Term) {
	if _, ok := zc.terms[t]; ok {
		return
	}
	r := zc.build(t)
	zc.check("term " + string(t.Op))
	C.Z3_inc_ref(zc.z, r)
	zc.terms[t] = r
}

func (zc *zctx) term(t *smt.Term) C.Z3_ast {
	if r, ok := zc.terms[t]; ok {
		return r
	}
	for _, a := range t.Args {
		zc.term(a)
	}
	zc.OnTerm(t)
	return zc.terms[t]
}

func (zc *zctx) args(t *smt.Term) []C.Z3_ast {
	out := make([]C.Z3_ast, len(t.Args)+1)
	for i, a := range t.Args {
		out[i] = zc.term(a)
	}
	return out
}

func (zc *zctx) rm(m smt.RoundingMode) C.Z3_ast {
	switch m {
	case smt.RNE:
		return C.Z3_mk_fpa_rne(zc.z)
	case smt.RNA:
		return C.Z3_mk_fpa_rna(zc.z)
	case smt.RTP:
		return C.Z3_mk_fpa_rtp(zc.z)
	case smt.RTN:
		return C.Z3_mk_fpa_rtn(zc.z)
	}
	return C.Z3_mk_fpa_rtz(zc.z)
}

func (zc *zctx) build(t *smt.Term) C.Z3_ast {
	z := zc.z
	a := zc.args(t)
	n := C.uint(len(t.Args))
	switch t.Op {
	case smt.OpTrue:
		return C.Z3_mk_true(z)
	case smt.OpFalse:
		return C.Z3_mk_false(z)
	case smt.OpNot:
		return C.Z3_mk_not(z, a[0])
	case smt.OpAnd:
		return C.Z3_mk_and(z, n, &a[0])
	case smt.OpOr:
		return C.Z3_mk_or(z, n, &a[0])
	case smt.OpImplies:
		return C.Z3_mk_implies(z, a[0], a[1])
	case smt.OpXor:
		return C.Z3_mk_xor(z, a[0], a[1])
	case smt.OpEq:
		return C.Z3_mk_eq(z, a[0], a[1])
	case smt.OpDistinct:
		return C.Z3_mk_distinct(z, n, &a[0])
	case smt.OpITE:
		return C.Z3_mk_ite(z, a[0], a[1], a[2])
	case smt.OpIntLit, smt.OpBVLit:
		cs := C.CString(t.Int.String())
		defer C.free(unsafe.Pointer(cs))
		return C.Z3_mk_numeral(z, cs, zc.sort(t.Sort))
	case smt.OpStrLit:
		chars := make([]C.uint, len(t.Runes)+1)
		for i, r := range t.Runes {
			chars[i] = C.uint(r)
		}
		return C.Z3_mk_u32string(z, C.uint(len(t.Runes)), &chars[0])
	case smt.OpFPLit:
		if t.Sort.EBits == 11 && t.Sort.SBits == 53 {
			return C.Z3_mk_fpa_numeral_double(z, C.double(math.Float64frombits(t.Bits)), zc.sort(t.Sort))
		}
		return C.Z3_mk_fpa_numeral_float(z, C.float(math.Float32frombits(uint32(t.Bits))), zc.sort(t.Sort))
	case smt.OpRM:
		return zc.rm(t.RM)
	case smt.OpAdd:
		return C.Z3_mk_add(z, n, &a[0])
	case smt.OpSub:
		return C.Z3_mk_sub(z, n, &a[0])
	case smt.OpMul:
		return C.Z3_mk_mul(z, n, &a[0])
	case smt.OpDiv:
		return C.Z3_mk_div(z, a[0], a[1])
	case smt.OpMod:
		return C.Z3_mk_mod(z, a[0], a[1])
	case smt.OpRem:
		return C.Z3_mk_rem(z, a[0], a[1])
	case smt.OpNeg:
		return C.Z3_mk_unary_minus(z, a[0])
	case smt.OpLt:
		return C.Z3_mk_lt(z, a[0], a[1])
	case smt.OpLe:
		return C.Z3_mk_le(z, a[0], a[1])
	case smt.OpGt:
		return C.Z3_mk_gt(z, a[0], a[1])
	case smt.OpGe:
		return C.Z3_mk_ge(z, a[0], a[1])
	case smt.OpToReal:
		return C.Z3_mk_int2real(z, a[0])
	case smt.OpToInt:
		return C.Z3_mk_real2int(z, a[0])
	case smt.OpIsInt:
		return C.Z3_mk_is_int(z, a[0])
	case smt.OpApp:
		d := zc.decl(t.Decl)
		if len(t.Args) == 0 {
			return C.Z3_mk_app(z, d, 0, nil)
		}
		return C.Z3_mk_app(z, d, n, &a[0])
	case smt.OpSelect:
		return C.Z3_mk_select(z, a[0], a[1])
	case smt.OpStore:
		return C.Z3_mk_store(z, a[0], a[1], a[2])
	case smt.OpConstArray:
		return C.Z3_mk_const_array(z, zc.sort(t.Sort.Domain()), a[0])
	case smt.OpSeqEmpty:
		return C.Z3_mk_seq_empty(z, zc.sort(t.Sort))
	case smt.OpSeqUnit:
		return C.Z3_mk_seq_unit(z, a[0])
	case smt.OpSeqConcat:
		return C.Z3_mk_seq_concat(z, n, &a[0])
	case smt.OpSeqLen:
		return C.Z3_mk_seq_length(z, a[0])
	case smt.OpSeqNth:
		return C.Z3_mk_seq_nth(z, a[0], a[1])
	case smt.OpSeqContains:
		return C.Z3_mk_seq_contains(z, a[0], a[1])
	case smt.OpSeqPrefix:
		return C.Z3_mk_seq_prefix(z, a[0], a[1])
	case smt.OpSeqSuffix:
		return C.Z3_mk_seq_suffix(z, a[0], a[1])
	case smt.OpSeqIndexOf:
		return C.Z3_mk_seq_index(z, a[0], a[1], a[2])
	case smt.OpSeqLastIndexOf:
		return C.Z3_mk_seq_last_index(z, a[0], a[1])
	case smt.OpSeqExtract:
		return C.Z3_mk_seq_extract(z, a[0], a[1], a[2])
	case smt.OpSeqAt:
		return C.Z3_mk_seq_at(z, a[0], a[1])
	case smt.OpSeqReplace:
		return C.Z3_mk_seq_replace(z, a[0], a[1], a[2])
	case smt.OpStrLt:
		return C.Z3_mk_str_lt(z, a[0], a[1])
	case smt.OpStrLe:
		return C.Z3_mk_str_le(z, a[0], a[1])
	case smt.OpStrToInt:
		return C.Z3_mk_str_to_int(z, a[0])
	case smt.OpStrFromInt:
		return C.Z3_mk_int_to_str(z, a[0])
	case smt.OpFPIsNaN:
		return C.Z3_mk_fpa_is_nan(z, a[0])
	case smt.OpFPIsZero:
		return C.Z3_mk_fpa_is_zero(z, a[0])
	case smt.OpFPIsNeg:
		return C.Z3_mk_fpa_is_negative(z, a[0])
	case smt.OpFPIsPos:
		return C.Z3_mk_fpa_is_positive(z, a[0])
	case smt.OpFPIsInf:
		return C.Z3_mk_fpa_is_infinite(z, a[0])
	case smt.OpFPIsNormal:
		return C.Z3_mk_fpa_is_normal(z, a[0])
	case smt.OpFPIsSubnormal:
		return C.Z3_mk_fpa_is_subnormal(z, a[0])
	case smt.OpFPAbs:
		return C.Z3_mk_fpa_abs(z, a[0])
	case smt.OpFPNeg:
		return C.Z3_mk_fpa_neg(z, a[0])
	case smt.OpFPAdd:
		return C.Z3_mk_fpa_add(z, a[0], a[1], a[2])
	case smt.OpFPSub:
		return C.Z3_mk_fpa_sub(z, a[0], a[1], a[2])
	case smt.OpFPMul:
		return C.Z3_mk_fpa_mul(z, a[0], a[1], a[2])
	case smt.OpFPDiv:
		return C.Z3_mk_fpa_div(z, a[0], a[1], a[2])
	case smt.OpFPRem:
		return C.Z3_mk_fpa_rem(z, a[0], a[1])
	case smt.OpFPSqrt:
		return C.Z3_mk_fpa_sqrt(z, a[0], a[1])
	case smt.OpFPMin:
		return C.Z3_mk_fpa_min(z, a[0], a[1])
	case smt.OpFPMax:
		return C.Z3_mk_fpa_max(z, a[0], a[1])
	case smt.OpFPLt:
		return C.Z3_mk_fpa_lt(z, a[0], a[1])
	case smt.OpFPLe:
		return C.Z3_mk_fpa_leq(z, a[0], a[1])
	case smt.OpFPGt:
		return C.Z3_mk_fpa_gt(z, a[0], a[1])
	case smt.OpFPGe:
		return C.Z3_mk_fpa_geq(z, a[0], a[1])
	case smt.OpFPEq:
		return C.Z3_mk_fpa_eq(z, a[0], a[1])
	case smt.OpFPRoundToInt:
		return C.Z3_mk_fpa_round_to_integral(z, a[0], a[1])
	case smt.OpFPToFP:
		switch t.Args[len(t.Args)-1].Sort.Kind {
		case smt.KindFP:
			return C.Z3_mk_fpa_to_fp_float(z, a[0], a[1], zc.sort(t.Sort))
		case smt.KindReal, smt.KindInt:
			return C.Z3_mk_fpa_to_fp_real(z, a[0], a[1], zc.sort(t.Sort))
		case smt.KindBV:
			if len(t.Args) == 1 {
				return C.Z3_mk_fpa_to_fp_bv(z, a[0], zc.sort(t.Sort))
			}
			return C.Z3_mk_fpa_to_fp_signed(z, a[0], a[1], zc.sort(t.Sort))
		}
	case smt.OpFPToFPUnsigned:
		return C.Z3_mk_fpa_to_fp_unsigned(z, a[0], a[1], zc.sort(t.Sort))
	case smt.OpFPToSBV:
		return C.Z3_mk_fpa_to_sbv(z, a[0], a[1], C.uint(t.Idx[0]))
	case smt.OpFPToUBV:
		return C.Z3_mk_fpa_to_ubv(z, a[0], a[1], C.uint(t.Idx[0]))
	case smt.OpFPToReal:
		return C.Z3_mk_fpa_to_real(z, a[0])
	case smt.OpFPToIEEEBV:
		return C.Z3_mk_fpa_to_ieee_bv(z, a[0])
	case smt.OpFPFromBits:
		return C.Z3_mk_fpa_fp(z, a[0], a[1], a[2])
	case smt.OpUBV2Int, smt.OpBV2Int:
		return C.Z3_mk_bv2int(z, a[0], false)
	case smt.OpInt2BV:
		return C.Z3_mk_int2bv(z, C.uint(t.Idx[0]), a[0])
	case smt.OpBVSlt:
		return C.Z3_mk_bvslt(z, a[0], a[1])
	case smt.OpBVSle:
		return C.Z3_mk_bvsle(z, a[0], a[1])
	case smt.OpBVUlt:
		return C.Z3_mk_bvult(z, a[0], a[1])
	case smt.OpBVUle:
		return C.Z3_mk_bvule(z, a[0], a[1])
	case smt.OpBVAdd:
		return C.Z3_mk_bvadd(z, a[0], a[1])
	case smt.OpBVSub:
		return C.Z3_mk_bvsub(z, a[0], a[1])
	case smt.OpBVMul:
		return C.Z3_mk_bvmul(z, a[0], a[1])
	case smt.OpBVAnd:
		return C.Z3_mk_bvand(z, a[0], a[1])
	case smt.OpBVOr:
		return C.Z3_mk_bvor(z, a[0], a[1])
	case smt.OpBVXor:
		return C.Z3_mk_bvxor(z, a[0], a[1])
	case smt.OpBVNot:
		return C.Z3_mk_bvnot(z, a[0])
	case smt.OpBVNeg:
		return C.Z3_mk_bvneg(z, a[0])
	case smt.OpBVShl:
		return C.Z3_mk_bvshl(z, a[0], a[1])
	case smt.OpBVLshr:
		return C.Z3_mk_bvlshr(z, a[0], a[1])
	case smt.OpExtract:
		return C.Z3_mk_extract(z, C.uint(t.Idx[0]), C.uint(t.Idx[1]), a[0])
	case smt.OpConcatBV:
		return C.Z3_mk_concat(z, a[0], a[1])
	case smt.OpZeroExt:
		return C.Z3_mk_zero_ext(z, C.uint(t.Idx[0]), a[0])
	case smt.OpSignExt:
		return C.Z3_mk_sign_ext(z, C.uint(t.Idx[0]), a[0])
	case smt.OpModelValue:
		if v, ok := zc.values[t.Name]; ok {
			return v
		}
		panic("z3cgo: unknown model value " + t.Name)
	case smt.OpAsArray:
		return C.Z3_mk_as_array(z, zc.decl(t.Decl))
	}
	// Builtins without an API constructor (e.g. seq.nth_i) reuse the declarations of Z3's own output.
	name := t.DeclName()
	if d, ok := zc.ops[name+"/"+strconv.Itoa(len(t.Args))]; ok {
		if len(t.Args) == 0 {
			return C.Z3_mk_app(z, d, 0, nil)
		}
		return C.Z3_mk_app(z, d, n, &a[0])
	}
	panic(fmt.Sprintf("z3cgo: cannot build %s", t))
}

// learn records the builtin declarations and model values of an AST Z3 produced.
func (zc *zctx) learn(a C.Z3_ast, seen map[C.Z3_ast]bool) {
	z := zc.z
	if seen[a] || C.Z3_get_ast_kind(z, a) != C.Z3_APP_AST {
		return
	}
	seen[a] = true
	app := C.Z3_to_app(z, a)
	d := C.Z3_get_app_decl(z, app)
	n := int(C.Z3_get_app_num_args(z, app))
	name := C.GoString(C.Z3_get_symbol_string(z, C.Z3_get_decl_name(z, d)))
	if C.Z3_get_decl_kind(z, d) == C.Z3_OP_UNINTERPRETED {
		if n == 0 && strings.Contains(name, "!val!") {
			if _, ok := zc.values[name]; !ok {
				C.Z3_inc_ref(z, a)
				zc.values[name] = a
			}
		}
	} else if _, ok := zc.ops[name+"/"+strconv.Itoa(n)]; !ok {
		zc.ops[name+"/"+strconv.Itoa(n)] = zc.keepDecl(d)
	}
	for i := 0; i < n; i++ {
		zc.learn(C.Z3_get_app_arg(z, app, C.uint(i)), seen)
	}
}

// fromZ3 converts an AST Z3 produced into a term of the context.
func (zc *zctx) fromZ3(a C.Z3_ast) (*smt.Term, error) {
	zc.learn(a, map[C.Z3_ast]bool{})
	s := C.GoString(C.Z3_ast_to_string(zc.z, a))
	return zc.c.ParseTerm(s)
}

// Simplify implements smt.Backend.
func (b *Backend) Simplify(c *smt.Context, t *smt.Term) *smt.Term {
	zc := b.ctx(c)
	r := C.Z3_simplify(zc.z, zc.term(t))
	zc.check("simplify")
	C.Z3_inc_ref(zc.z, r)
	defer C.Z3_dec_ref(zc.z, r)
	out, err := zc.fromZ3(r)
	if err != nil {
		panic(fmt.Sprintf("z3cgo: %v", err))
	}
	return out
}

// NewSolver implements smt.Backend.
func (b *Backend) NewSolver(c *smt.Context, timeout time.Duration) (smt.Solver, error) {
	zc := b.ctx(c)
	s := C.Z3_mk_solver(zc.z)
	C.Z3_solver_inc_ref(zc.z, s)
	if timeout > 0 {
		p := C.Z3_mk_params(zc.z)
		C.Z3_params_inc_ref(zc.z, p)
		C.Z3_params_set_uint(zc.z, p, zc.sym("timeout"), C.uint(timeout.Milliseconds()))
		C.Z3_solver_set_params(zc.z, s, p)
		C.Z3_params_dec_ref(zc.z, p)
	}
	return &solver{zc: zc, s: s}, nil
}

type solver struct {
	zc    *zctx
	s     C.Z3_solver
	model C.Z3_model
}

func (s *solver) dropModel() {
	if s.model != nil {
		C.Z3_model_dec_ref(s.zc.z, s.model)
		s.model = nil
	}
}

func (s *solver) Push() { s.dropModel(); C.Z3_solver_push(s.zc.z, s.s) }
func (s *solver) Pop()  { s.dropModel(); C.Z3_solver_pop(s.zc.z, s.s, 1) }

func (s *solver) Assert(ts ...*smt.Term) {
	s.dropModel()
	for _, t := range ts {
		C.Z3_solver_assert(s.zc.z, s.s, s.zc.term(t))
	}
	s.zc.check("assert")
}

func (s *solver) Check() (smt.Status, error) {
	s.dropModel()
	r := C.Z3_solver_check(s.zc.z, s.s)
	if code := C.Z3_get_error_code(s.zc.z); code != C.Z3_OK {
		return smt.Unknown, fmt.Errorf("z3cgo: check: %s", C.GoString(C.Z3_get_error_msg(s.zc.z, code)))
	}
	switch r {
	case C.Z3_L_TRUE:
		s.model = C.Z3_solver_get_model(s.zc.z, s.s)
		C.Z3_model_inc_ref(s.zc.z, s.model)
		return smt.Sat, nil
	case C.Z3_L_FALSE:
		return smt.Unsat, nil
	}
	return smt.Unknown, nil
}

func (s *solver) ReasonUnknown() string {
	return C.GoString(C.Z3_solver_get_reason_unknown(s.zc.z, s.s))
}

func (s *solver) Close() {
	s.dropModel()
	C.Z3_solver_dec_ref(s.zc.z, s.s)
}

func (s *solver) Model() smt.Model { return &model{s} }

type model struct{ s *solver }

func (m *model) Eval(t *smt.Term, completion bool) (*smt.Term, error) {
	s := m.s
	if s.model == nil {
		return nil, fmt.Errorf("z3cgo: no model")
	}
	var out C.Z3_ast
	if !C.Z3_model_eval(s.zc.z, s.model, s.zc.term(t), C.bool(completion), &out) {
		return nil, fmt.Errorf("z3cgo: cannot evaluate %s", t)
	}
	C.Z3_inc_ref(s.zc.z, out)
	defer C.Z3_dec_ref(s.zc.z, out)
	return s.zc.fromZ3(out)
}
