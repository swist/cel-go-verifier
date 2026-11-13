package dev.cel.verifier;

import com.microsoft.z3.BoolExpr;
import com.microsoft.z3.Solver;
import com.microsoft.z3.Status;
import java.io.IOException;
import java.io.UncheckedIOException;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.nio.file.StandardOpenOption;

/**
 * Records every solver interaction of the verifier as an SMT-LIB2 transcript, one file per test.
 * Enabled by the {@code smtdump.dir} system property. Not part of the upstream verifier: this is
 * injected by javaref/scripts/patch.py to produce goldens for the Go port.
 */
public final class SmtDump {
  private static final String DIR = System.getProperty("smtdump.dir");
  private static volatile String currentTest;
  private static int queryCounter;

  public static synchronized void startTest(String name) {
    currentTest = name.replaceAll("[^A-Za-z0-9_.\\[\\]=,-]", "_");
    if (currentTest.length() > 200) {
      currentTest = currentTest.substring(0, 160) + "_" + Integer.toHexString(name.hashCode());
    }
    queryCounter = 0;
    if (DIR != null) {
      try {
        Files.deleteIfExists(path());
      } catch (IOException e) {
        throw new UncheckedIOException(e);
      }
    }
  }

  private static Path path() {
    return Paths.get(DIR, currentTest + ".smt2");
  }

  private static synchronized void write(String s) {
    if (DIR == null || currentTest == null) {
      return;
    }
    try {
      Files.createDirectories(Paths.get(DIR));
      Files.write(
          path(),
          s.getBytes(StandardCharsets.UTF_8),
          StandardOpenOption.CREATE,
          StandardOpenOption.APPEND);
    } catch (IOException e) {
      throw new UncheckedIOException(e);
    }
  }

  /** Called whenever the verifier creates a solver: starts a new query section. */
  public static Solver newSolver(Solver solver) {
    String method = "unknown";
    for (StackTraceElement e : Thread.currentThread().getStackTrace()) {
      if (e.getClassName().equals(CelVerifierZ3Impl.class.getName())) {
        switch (e.getMethodName()) {
          case "isSatisfiable":
          case "isAlwaysTrue":
          case "verifyEquivalence":
          case "verifyImplication":
            method = e.getMethodName();
            break;
          default:
        }
      }
    }
    synchronized (SmtDump.class) {
      queryCounter++;
      write(";; query " + queryCounter + " " + method + "\n");
    }
    return solver;
  }

  public static void push(Solver solver) {
    write("(push)\n");
    solver.push();
  }

  public static void pop(Solver solver) {
    write("(pop)\n");
    solver.pop();
  }

  public static void add(Solver solver, BoolExpr... assertions) {
    StringBuilder sb = new StringBuilder();
    for (BoolExpr a : assertions) {
      sb.append("(assert ").append(a.toString().replace('\n', ' ')).append(")\n");
    }
    write(sb.toString());
    solver.add(assertions);
  }

  public static Status check(Solver solver) {
    Status status = solver.check();
    write("(check-sat) ; " + status + "\n");
    return status;
  }

  private SmtDump() {}
}
