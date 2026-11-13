package dev.cel.verifier;

import org.junit.runner.Description;
import org.junit.runner.notification.RunListener;

/** Points SmtDump at the running test (javaref harness). */
public final class SmtDumpListener extends RunListener {
  @Override
  public void testStarted(Description description) {
    String cls = description.getClassName();
    cls = cls.substring(cls.lastIndexOf('.') + 1);
    SmtDump.startTest(cls + "." + description.getMethodName());
  }
}
