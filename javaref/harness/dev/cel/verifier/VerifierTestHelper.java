package dev.cel.verifier;

import static java.nio.charset.StandardCharsets.UTF_8;

import com.google.common.io.Resources;
import java.io.IOException;
import java.net.URL;
import java.util.Optional;

/** Classpath-based replacement for the Bazel runfiles helper (javaref harness). */
final class VerifierTestHelper {

  static String loadVerificationPolicyYaml(String filename) throws IOException {
    return load("policy/verification/" + filename);
  }

  static String loadConformancePolicyYaml(String policyDir) throws IOException {
    return load(String.format("conformance/testdata/%s/policy.yaml", policyDir));
  }

  static Optional<String> maybeLoadConformanceConfigYaml(String policyDir) throws IOException {
    return maybeLoad(String.format("conformance/testdata/%s/config.yaml", policyDir));
  }

  private static String load(String path) throws IOException {
    return maybeLoad(path).orElseThrow(() -> new IOException("Resource not found: " + path));
  }

  private static Optional<String> maybeLoad(String path) throws IOException {
    URL url = VerifierTestHelper.class.getClassLoader().getResource(path);
    if (url == null) {
      return Optional.empty();
    }
    return Optional.of(Resources.toString(url, UTF_8));
  }

  private VerifierTestHelper() {}
}
