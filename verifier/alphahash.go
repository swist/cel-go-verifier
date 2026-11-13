package verifier

import (
	"encoding/binary"
	"math"
	"strings"
	"unicode/utf16"

	"cel.dev/cel-go/common/ast"
	"cel.dev/cel-go/common/types"
	"cel.dev/cel-go/common/types/ref"
)

// alphaSignature identifies an expression up to renaming of its bound
// variables: a hash in which bound variables are de Bruijn indices, and the
// free variables in order of appearance. It's computed exactly like cel-java's
// CelAstAlphaHasher (a Guava FarmHash fingerprint over the same byte stream).
type alphaSignature struct {
	staticHash uint64
	freeVars   []ast.Expr
}

type alphaScope struct {
	name   string
	parent *alphaScope
}

func (s *alphaScope) indexOf(name string) int {
	idx := 0
	for cur := s; cur != nil; cur = cur.parent {
		if cur.name == name {
			return idx
		}
		idx++
	}
	return -1
}

type alphaHasher struct {
	buf      []byte
	a        *ast.AST
	freeIdx  map[string]int
	freeVars []ast.Expr
}

func computeAlphaSignature(e ast.Expr, a *ast.AST) alphaSignature {
	h := &alphaHasher{a: a, freeIdx: map[string]int{}}
	h.hash(e, nil)
	return alphaSignature{farmFingerprint64(h.buf), h.freeVars}
}

func (h *alphaHasher) putString(s string) { h.buf = append(h.buf, s...) }
func (h *alphaHasher) putByte(b byte)     { h.buf = append(h.buf, b) }
func (h *alphaHasher) putInt(i int32)     { h.buf = binary.LittleEndian.AppendUint32(h.buf, uint32(i)) }
func (h *alphaHasher) putLong(i int64)    { h.buf = binary.LittleEndian.AppendUint64(h.buf, uint64(i)) }
func (h *alphaHasher) putBool(b bool) {
	if b {
		h.putByte(1)
	} else {
		h.putByte(0)
	}
}

var exprKindNames = map[ast.ExprKind]string{
	ast.LiteralKind: "CONSTANT", ast.IdentKind: "IDENT", ast.SelectKind: "SELECT", ast.CallKind: "CALL",
	ast.ListKind: "LIST", ast.StructKind: "STRUCT", ast.MapKind: "MAP", ast.ComprehensionKind: "COMPREHENSION",
	ast.UnspecifiedExprKind: "NOT_SET",
}

func (h *alphaHasher) hash(e ast.Expr, scope *alphaScope) {
	if v := referenceValue(h.a, e); v != nil {
		h.putString("CONSTANT")
		h.hashConstant(v)
		return
	}
	h.putString(exprKindNames[e.Kind()])
	switch e.Kind() {
	case ast.LiteralKind:
		h.hashConstant(e.AsLiteral())
	case ast.IdentKind:
		name := e.AsIdent()
		if b := scopeIndex(scope, name); b >= 0 {
			h.putByte(0)
			h.putInt(int32(b))
		} else {
			free := strings.TrimPrefix(name, ".")
			idx, ok := h.freeIdx[free]
			if !ok {
				h.freeVars = append(h.freeVars, e)
				idx = len(h.freeVars) - 1
				h.freeIdx[free] = idx
			}
			h.putByte(1)
			h.putInt(int32(idx))
		}
	case ast.SelectKind:
		s := e.AsSelect()
		h.hash(s.Operand(), scope)
		h.putString(s.FieldName())
		h.putBool(s.IsTestOnly())
	case ast.CallKind:
		c := e.AsCall()
		h.putString(c.FunctionName())
		h.putBool(c.IsMemberFunction())
		if c.IsMemberFunction() {
			h.hash(c.Target(), scope)
		}
		h.putInt(int32(len(c.Args())))
		for _, arg := range c.Args() {
			h.hash(arg, scope)
		}
	case ast.ListKind:
		l := e.AsList()
		h.putInt(int32(len(l.Elements())))
		for i, el := range l.Elements() {
			h.putBool(l.IsOptional(int32(i)))
			h.hash(el, scope)
		}
	case ast.StructKind:
		s := e.AsStruct()
		h.putString(s.TypeName())
		h.putInt(int32(len(s.Fields())))
		for _, f := range s.Fields() {
			fe := f.AsStructField()
			h.putString(fe.Name())
			h.putBool(fe.IsOptional())
			h.hash(fe.Value(), scope)
		}
	case ast.MapKind:
		m := e.AsMap()
		h.putInt(int32(len(m.Entries())))
		for _, en := range m.Entries() {
			me := en.AsMapEntry()
			h.putBool(me.IsOptional())
			h.hash(me.Key(), scope)
			h.hash(me.Value(), scope)
		}
	case ast.ComprehensionKind:
		c := e.AsComprehension()
		h.hash(c.IterRange(), scope)
		h.hash(c.AccuInit(), scope)
		h.putBool(c.AccuVar() != "")
		h.putBool(c.IterVar() != "")
		h.putBool(c.IterVar2() != "")
		loop := scope
		if c.IterVar() != "" {
			loop = &alphaScope{c.IterVar(), loop}
		}
		if c.IterVar2() != "" {
			loop = &alphaScope{c.IterVar2(), loop}
		}
		if c.AccuVar() != "" {
			loop = &alphaScope{c.AccuVar(), loop}
		}
		h.hash(c.LoopCondition(), loop)
		h.hash(c.LoopStep(), loop)
		res := scope
		if c.AccuVar() != "" {
			res = &alphaScope{c.AccuVar(), res}
		}
		h.hash(c.Result(), res)
	}
}

func scopeIndex(s *alphaScope, name string) int {
	if s == nil {
		return -1
	}
	return s.indexOf(name)
}

func (h *alphaHasher) hashConstant(v ref.Val) {
	switch val := v.(type) {
	case types.Null:
		h.putString("NULL_VALUE")
		h.putInt(0)
	case types.Bool:
		h.putString("BOOLEAN_VALUE")
		h.putBool(bool(val))
	case types.Int:
		h.putString("INT64_VALUE")
		h.putLong(int64(val))
	case types.Uint:
		h.putString("UINT64_VALUE")
		h.putLong(int64(val))
	case types.Double:
		h.putString("DOUBLE_VALUE")
		h.putLong(int64(math.Float64bits(float64(val))))
	case types.String:
		h.putString("STRING_VALUE")
		h.putInt(int32(len(utf16.Encode([]rune(string(val))))))
		h.putString(string(val))
	case types.Bytes:
		h.putString("BYTES_VALUE")
		h.putInt(int32(len(val)))
		h.buf = append(h.buf, val...)
	default:
		h.putString("NOT_SET")
	}
}

// referenceValue returns the constant an identifier refers to (e.g. an enum value), if any.
func referenceValue(a *ast.AST, e ast.Expr) ref.Val {
	if r, ok := a.ReferenceMap()[e.ID()]; ok && r != nil && r.Value != nil {
		return r.Value
	}
	return nil
}
