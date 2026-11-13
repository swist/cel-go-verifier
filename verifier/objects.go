package verifier

import (
	"math/big"
	"strings"

	"cel.dev/cel-go/common/types/ref"

	"github.com/swist/cel-go-verifier/smt"
)

// Opaque values of extension libraries (e.g. Kubernetes' quantities or IP
// addresses) are encoded as messages of their type name whose fields hold a
// canonical representation of the value. Message extensionality then makes
// two such values equal exactly when their representations are.

// ObjectField is a field of an object's representation.
type ObjectField struct {
	Name  string
	Value *smt.Term
}

// IsOpaque tests whether v is a value of the named opaque or object type.
func (ts *TypeSystem) IsOpaque(v *smt.Term, typeName string) *smt.Term {
	c := ts.c
	return c.MkAnd(ts.IsMessage(v), c.MkEq(ts.GetMsgTypeName(ts.GetMessageRef(v)), MkZ3String(c, typeName)))
}

// DefineObject constrains the message reference ref to an object of typeName
// with exactly the given fields, and returns the object.
func (ts *TypeSystem) DefineObject(sink func(*smt.Term), ref *smt.Term, typeName string, fields ...ObjectField) *smt.Term {
	c := ts.c
	values := c.MkConstArray(c.StringSort(), ts.MkUnknown())
	presence := c.MkConstArray(c.StringSort(), c.MkFalse())
	for _, f := range fields {
		key := MkZ3String(c, f.Name)
		values = c.MkStore(values, key, f.Value)
		presence = c.MkStore(presence, key, c.MkTrue())
	}
	sink(c.MkEq(ts.GetMsgTypeName(ref), MkZ3String(c, typeName)))
	sink(c.MkEq(ts.GetMsgValues(ref), values))
	sink(c.MkEq(ts.GetMsgPresence(ref), presence))
	return ts.WrapMessage(ref)
}

// ObjectField returns the field of an object's representation.
func (ts *TypeSystem) ObjectField(v *smt.Term, name string) *smt.Term {
	c := ts.c
	return c.MkSelect(ts.GetMsgValues(ts.GetMessageRef(v)), MkZ3String(c, name))
}

// StringLiteral returns the value of v if it is a string literal.
func (ts *TypeSystem) StringLiteral(v *smt.Term) (string, bool) {
	if v.IsAppOf(ts.stringCons.Decl) && v.Args[0].Op == smt.OpStrLit {
		return string(v.Args[0].Runes), true
	}
	return "", false
}

// IntLiteral returns the value of v if it is an int literal.
func (ts *TypeSystem) IntLiteral(v *smt.Term) (*big.Int, bool) {
	if v.IsAppOf(ts.intCons.Decl) && v.Args[0].IsIntLit() {
		return v.Args[0].Int, true
	}
	return nil, false
}

// BoolLiteral returns the value of v if it is a bool literal.
func (ts *TypeSystem) BoolLiteral(v *smt.Term) (bool, bool) {
	if v.IsAppOf(ts.boolCons.Decl) && (v.Args[0].IsTrue() || v.Args[0].IsFalse()) {
		return v.Args[0].IsTrue(), true
	}
	return false, false
}

// MessageField is a field of a message in a witness.
type MessageField struct {
	// Value is the field's value, or nil if it isn't representable exactly.
	Value ref.Val
	// Display is how the witness shows the value.
	Display string
}

// MessageFormatter displays the messages of a type in witnesses. It returns
// the display and, if it can build it, the value; ok is false to fall back to
// the default display.
type MessageFormatter func(fields map[string]MessageField) (val ref.Val, display string, ok bool)

// MessageFormatters installs formatters for messages (or encoded opaque values) by type name.
func MessageFormatters(f map[string]MessageFormatter) Option {
	return func(v *Verifier) error {
		if v.formatters == nil {
			v.formatters = map[string]MessageFormatter{}
		}
		for k, fn := range f {
			v.formatters[k] = fn
		}
		return nil
	}
}

// BigIntField parses a field holding an int, including one beyond int64.
func BigIntField(f MessageField) (*big.Int, bool) {
	return new(big.Int).SetString(strings.TrimSuffix(f.Display, "u"), 10)
}

// MessageRefOf returns the reference of v if v is built as a message.
func (ts *TypeSystem) MessageRefOf(v *smt.Term) (*smt.Term, bool) {
	if v.IsAppOf(ts.messageCons.Decl) {
		return v.Args[0], true
	}
	return nil, false
}

// ObjectConstraint constrains the representation of a value of an object
// type, e.g. a variable declared with an extension library's opaque type.
type ObjectConstraint func(ts *TypeSystem, v *smt.Term) *smt.Term

// ObjectConstraints installs constraints on values of object types, by type name.
func ObjectConstraints(f map[string]ObjectConstraint) Option {
	return func(v *Verifier) error {
		if v.objConstraints == nil {
			v.objConstraints = map[string]ObjectConstraint{}
		}
		for k, fn := range f {
			v.objConstraints[k] = fn
		}
		return nil
	}
}

// HasExactFields constrains an object to have exactly the named fields.
func (ts *TypeSystem) HasExactFields(v *smt.Term, names ...string) *smt.Term {
	c := ts.c
	ref := ts.GetMessageRef(v)
	values := c.MkConstArray(c.StringSort(), ts.MkUnknown())
	presence := c.MkConstArray(c.StringSort(), c.MkFalse())
	for _, n := range names {
		key := MkZ3String(c, n)
		values = c.MkStore(values, key, c.MkSelect(ts.GetMsgValues(ref), key))
		presence = c.MkStore(presence, key, c.MkTrue())
	}
	return c.MkAnd(c.MkEq(ts.GetMsgValues(ref), values), c.MkEq(ts.GetMsgPresence(ref), presence))
}
