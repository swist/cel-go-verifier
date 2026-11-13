package verifier

import (
	"cel.dev/cel-go/common/types"
	"google.golang.org/protobuf/reflect/protoreflect"
)

// ProtoTypeProvider models the messages of proto files, and the files they import.
type ProtoTypeProvider struct {
	provider types.Provider
	names    []string
	enums    map[string]bool
}

// NewProtoTypeProvider lists the messages of files and their imports, in
// declaration order. provider (e.g. env.CELTypeProvider()) supplies field types.
func NewProtoTypeProvider(provider types.Provider, files ...protoreflect.FileDescriptor) *ProtoTypeProvider {
	p := &ProtoTypeProvider{provider: provider, enums: map[string]bool{}}
	seen := map[string]bool{}
	var visitFile func(protoreflect.FileDescriptor)
	var visitMsgs func(protoreflect.MessageDescriptors)
	visitMsgs = func(ms protoreflect.MessageDescriptors) {
		for i := 0; i < ms.Len(); i++ {
			m := ms.Get(i)
			if m.IsMapEntry() {
				continue
			}
			p.names = append(p.names, string(m.FullName()))
			fs := m.Fields()
			for j := 0; j < fs.Len(); j++ {
				if f := fs.Get(j); f.Kind() == protoreflect.EnumKind && !f.IsList() && !f.IsMap() {
					p.enums[string(m.FullName())+"."+string(f.Name())] = true
				}
			}
			visitMsgs(m.Messages())
		}
	}
	visitFile = func(f protoreflect.FileDescriptor) {
		if seen[f.Path()] {
			return
		}
		seen[f.Path()] = true
		visitMsgs(f.Messages())
		imports := f.Imports()
		for i := 0; i < imports.Len(); i++ {
			visitFile(imports.Get(i).FileDescriptor)
		}
	}
	for _, f := range files {
		visitFile(f)
	}
	return p
}

// WithOrder overrides the order of the message types.
func (p *ProtoTypeProvider) WithOrder(names []string) *ProtoTypeProvider {
	q := *p
	q.names = names
	return &q
}

// StructTypeNames implements TypeProvider.
func (p *ProtoTypeProvider) StructTypeNames() []string { return p.names }

// FieldType implements TypeProvider.
func (p *ProtoTypeProvider) FieldType(message, field string) (FieldInfo, bool) {
	ft, ok := p.provider.FindStructFieldType(message, field)
	if !ok {
		return FieldInfo{}, false
	}
	return FieldInfo{Type: ft.Type, IsEnum: p.enums[message+"."+field]}, true
}
