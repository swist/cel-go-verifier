package dev.cel.verifier;

import java.lang.reflect.Field;
import java.lang.reflect.Modifier;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Paths;
import java.util.Collection;
import java.util.Map;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.JUnit4;

/** Dumps the parameterized test case enums of the verifier tests as JSON (javaref harness). */
@RunWith(JUnit4.class)
public final class DumpTestCasesTest {
  @Test
  public void dump() throws Exception {
    String dir = System.getProperty("smtdump.dir");
    if (dir == null) {
      return;
    }
    StringBuilder sb = new StringBuilder("{\n");
    boolean firstClass = true;
    for (Class<?> testClass :
        new Class<?>[] {
          CelVerifierZ3ImplTest.class,
          CelPolicyVerifierImplTest.class,
          CanonicalizationOptimizerTest.class,
          dev.cel.verifier.tools.CelVerifierToolTest.class
        }) {
      for (Class<?> nested : testClass.getDeclaredClasses()) {
        if (!nested.isEnum()) {
          continue;
        }
        if (!firstClass) {
          sb.append(",\n");
        }
        firstClass = false;
        sb.append("  ").append(quote(testClass.getSimpleName() + "." + nested.getSimpleName()))
            .append(": [");
        boolean firstConst = true;
        for (Object constant : nested.getEnumConstants()) {
          if (!firstConst) {
            sb.append(",");
          }
          firstConst = false;
          sb.append("\n    {\"name\": ").append(quote(((Enum<?>) constant).name()));
          for (Field f : nested.getDeclaredFields()) {
            if (Modifier.isStatic(f.getModifiers()) || f.isSynthetic()) {
              continue;
            }
            f.setAccessible(true);
            sb.append(", ").append(quote(f.getName())).append(": ").append(json(f.get(constant)));
          }
          sb.append("}");
        }
        sb.append("\n  ]");
      }
    }
    // The order of the message types each test environment's type provider lists.
    for (Class<?> testClass :
        new Class<?>[] {CelVerifierZ3ImplTest.class, CelPolicyVerifierImplTest.class}) {
      for (Field f : testClass.getDeclaredFields()) {
        if (!Modifier.isStatic(f.getModifiers())
            || !dev.cel.bundle.Cel.class.isAssignableFrom(f.getType())) {
          continue;
        }
        f.setAccessible(true);
        dev.cel.bundle.Cel cel = (dev.cel.bundle.Cel) f.get(null);
        sb.append(",\n  ").append(quote("types:" + testClass.getSimpleName() + "." + f.getName())).append(": [");
        boolean first = true;
        for (dev.cel.common.types.CelType t : cel.getTypeProvider().types()) {
          if (!first) {
            sb.append(", ");
          }
          first = false;
          sb.append(quote(t.name()));
        }
        sb.append("]");
      }
    }
    sb.append("\n}\n");
    Files.write(
        Paths.get(dir, "..", "testcases.json"), sb.toString().getBytes(StandardCharsets.UTF_8));
  }

  private static String json(Object o) {
    if (o == null) {
      return "null";
    }
    if (o instanceof String) {
      return quote((String) o);
    }
    if (o instanceof Number || o instanceof Boolean) {
      return o.toString();
    }
    if (o instanceof Enum) {
      return quote(((Enum<?>) o).name());
    }
    if (o instanceof Collection) {
      StringBuilder sb = new StringBuilder("[");
      boolean first = true;
      for (Object e : (Collection<?>) o) {
        if (!first) {
          sb.append(", ");
        }
        first = false;
        sb.append(json(e));
      }
      return sb.append("]").toString();
    }
    if (o instanceof Map) {
      StringBuilder sb = new StringBuilder("{");
      boolean first = true;
      for (Map.Entry<?, ?> e : ((Map<?, ?>) o).entrySet()) {
        if (!first) {
          sb.append(", ");
        }
        first = false;
        sb.append(quote(String.valueOf(e.getKey()))).append(": ").append(json(e.getValue()));
      }
      return sb.append("}").toString();
    }
    if (o instanceof java.util.Optional) {
      return ((java.util.Optional<?>) o).map(DumpTestCasesTest::json).orElse("null");
    }
    return "{\"$class\": " + quote(o.getClass().getName()) + ", \"$string\": " + quote(o.toString()) + "}";
  }

  private static String quote(String s) {
    StringBuilder sb = new StringBuilder("\"");
    for (char c : s.toCharArray()) {
      switch (c) {
        case '"':
          sb.append("\\\"");
          break;
        case '\\':
          sb.append("\\\\");
          break;
        case '\n':
          sb.append("\\n");
          break;
        case '\t':
          sb.append("\\t");
          break;
        case '\r':
          sb.append("\\r");
          break;
        default:
          if (c < 0x20 || c > 0x7e) {
            sb.append(String.format("\\u%04x", (int) c));
          } else {
            sb.append(c);
          }
      }
    }
    return sb.append("\"").toString();
  }
}
