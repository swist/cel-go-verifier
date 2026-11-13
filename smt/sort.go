// Package smt is a small, dependency free SMT-LIB2 term layer modelled on the
// Z3 Java API.
//
// Terms are hash-consed: building the same term twice yields the same *Term,
// so terms can be compared with == exactly like Z3 ASTs compare by identity.
// Nothing is simplified while building terms, so the terms (and their SMT-LIB2
// printing) match what the Z3 API builds for the same sequence of calls. The
// operations that need a solver (simplification, satisfiability, model
// evaluation) are delegated to a Backend.
package smt

import (
	"fmt"
	"strings"
)

// SortKind identifies the kind of a Sort.
type SortKind int

// Sort kinds.
const (
	KindBool SortKind = iota
	KindInt
	KindReal
	KindString
	KindChar
	KindSeq
	KindArray
	KindFP
	KindBV
	KindRoundingMode
	KindUninterpreted
	KindDatatype
)

// Sort is an SMT sort. Sorts are interned per Context and compare with ==.
type Sort struct {
	Kind SortKind
	// Name of an uninterpreted or datatype sort.
	Name string
	// Params holds the element sort of a sequence, or the domain and range of an array.
	Params []*Sort
	// EBits and SBits of a floating point sort.
	EBits, SBits int
	// Size of a bit-vector sort.
	Size int
	// Datatype describes a datatype sort.
	Datatype *Datatype

	key string
}

func (s *Sort) String() string {
	switch s.Kind {
	case KindBool:
		return "Bool"
	case KindInt:
		return "Int"
	case KindReal:
		return "Real"
	case KindString:
		return "String"
	case KindChar:
		return "Unicode"
	case KindSeq:
		return "(Seq " + s.Params[0].String() + ")"
	case KindArray:
		return "(Array " + s.Params[0].String() + " " + s.Params[1].String() + ")"
	case KindFP:
		return fmt.Sprintf("(_ FloatingPoint %d %d)", s.EBits, s.SBits)
	case KindBV:
		return fmt.Sprintf("(_ BitVec %d)", s.Size)
	case KindRoundingMode:
		return "RoundingMode"
	default:
		return quoteSymbol(s.Name)
	}
}

// Elem returns the element sort of a sequence sort.
func (s *Sort) Elem() *Sort { return s.Params[0] }

// Domain returns the domain of an array sort.
func (s *Sort) Domain() *Sort { return s.Params[0] }

// Range returns the range of an array sort.
func (s *Sort) Range() *Sort { return s.Params[1] }

// IsSeqLike reports whether s is a sequence or string sort.
func (s *Sort) IsSeqLike() bool { return s.Kind == KindSeq || s.Kind == KindString }

// Datatype is an algebraic datatype with non-recursive constructors.
type Datatype struct {
	Name         string
	Constructors []*Constructor
}

// Constructor is a datatype constructor.
type Constructor struct {
	Name string
	// TesterName is the name Z3 Java gives the recognizer. Z3 prints recognizers as (_ is Name).
	TesterName string
	FieldNames []string
	FieldSorts []*Sort

	Decl      *FuncDecl
	Tester    *FuncDecl
	Accessors []*FuncDecl
}

// ConstructorSpec describes a constructor to be created by MkDatatypeSort.
type ConstructorSpec struct {
	Name       string
	TesterName string
	FieldNames []string
	FieldSorts []*Sort
}

// DeclKind distinguishes uninterpreted functions from datatype functions.
type DeclKind int

// Declaration kinds.
const (
	DeclUninterpreted DeclKind = iota
	DeclConstructor
	DeclTester
	DeclAccessor
)

// FuncDecl is a function declaration. Declarations are interned per Context.
type FuncDecl struct {
	Name   string
	Domain []*Sort
	Range  *Sort
	Kind   DeclKind
	// Cons is the constructor of a constructor, tester or accessor.
	Cons *Constructor
	// Field is the field index of an accessor.
	Field int

	key string
}

func (d *FuncDecl) String() string { return d.Name }

func sortListKey(sorts []*Sort) string {
	var sb strings.Builder
	for i, s := range sorts {
		if i > 0 {
			sb.WriteByte(',')
		}
		sb.WriteString(s.key)
	}
	return sb.String()
}
