package dev.cel.verifier;

import dev.cel.common.CelFunctionDecl;
import dev.cel.common.CelOverloadDecl;
import dev.cel.common.types.CelType;
import dev.cel.verifier.axioms.CelZ3FunctionAxiom;
import dev.cel.verifier.axioms.CelZ3StandardAxioms;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Paths;
import java.util.stream.Collectors;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.JUnit4;

/** Dumps the declarations of the standard axioms as JSON (javaref harness). */
@RunWith(JUnit4.class)
public final class DumpAxiomDeclsTest {
  @Test
  public void dump() throws Exception {
    String dir = System.getProperty("smtdump.dir");
    if (dir == null) {
      return;
    }
    StringBuilder sb = new StringBuilder("[\n");
    boolean first = true;
    for (CelZ3FunctionAxiom axiom : CelZ3StandardAxioms.functionAxioms()) {
      CelFunctionDecl decl = axiom.declaration();
      if (!first) {
        sb.append(",\n");
      }
      first = false;
      sb.append("  {\"name\": \"").append(decl.name()).append("\", \"overloads\": [");
      boolean firstO = true;
      for (CelOverloadDecl o : decl.overloads()) {
        if (!firstO) {
          sb.append(", ");
        }
        firstO = false;
        sb.append("\n    {\"id\": \"").append(o.overloadId()).append("\", \"params\": [")
            .append(
                o.parameterTypes().stream()
                    .map(t -> "\"" + typeString(t) + "\"")
                    .collect(Collectors.joining(", ")))
            .append("], \"result\": \"").append(typeString(o.resultType()))
            .append("\", \"member\": ").append(o.isInstanceFunction())
            .append(", \"translated\": ")
            .append(axiom.overloadTranslators().containsKey(o.overloadId()))
            .append("}");
      }
      sb.append("]}");
    }
    sb.append("\n]\n");
    Files.write(Paths.get(dir, "..", "axiom_decls.json"), sb.toString().getBytes(StandardCharsets.UTF_8));
  }

  private static String typeString(CelType t) {
    return t.kind() + ":" + t.name();
  }
}
