#!/usr/bin/env bash
# Copies the cel-java verifier sources (and the test inputs they need) into
# javaref/src so that the reference implementation can be built with Maven
# against the published dev.cel jars, then applies the SMT-dump hook.
#
# Usage: javaref/scripts/sync.sh <cel-java checkout> <cel-conformance checkout> <cel-policy checkout>
set -euo pipefail
CEL_JAVA=$(cd "$1" && pwd)
CONFORMANCE=$(cd "$2" && pwd)
POLICY=$(cd "$3" && pwd)
HERE=$(cd "$(dirname "$0")/.." && pwd)
SRC=$HERE/src
rm -rf "$SRC"
mkdir -p "$SRC/main/java/dev/cel" "$SRC/test/java/dev/cel" "$SRC/main/proto" "$SRC/test/resources"

cp -r "$CEL_JAVA/verifier/src/main/java/dev/cel/verifier" "$SRC/main/java/dev/cel/"
cp -r "$CEL_JAVA/verifier/src/test/java/dev/cel/verifier" "$SRC/test/java/dev/cel/"
find "$SRC" -name BUILD.bazel -delete
# The REPL is out of scope for the port (and needs jline).
rm -f "$SRC"/main/java/dev/cel/verifier/tools/CelVerifierRepl.java "$SRC"/test/java/dev/cel/verifier/tools/CelVerifierReplTest.java
# Newer than the published dev.cel jars; shadows the jar's copy on the classpath.
mkdir -p "$SRC/main/java/dev/cel/common/internal"
cp "$CEL_JAVA/common/src/main/java/dev/cel/common/internal/ProtoTimeUtils.java" "$SRC/main/java/dev/cel/common/internal/"
mkdir -p "$SRC/main/java/dev/cel/policy/testing"
cp "$CEL_JAVA/policy/src/main/java/dev/cel/policy/testing/K8sTagHandler.java" "$SRC/main/java/dev/cel/policy/testing/"

# Protos used by the tests.
mkdir -p "$SRC/main/proto/cel/expr/conformance/proto3" "$SRC/main/proto/cel/expr/conformance/proto2"
cp "$CONFORMANCE/proto/cel/expr/conformance/proto3/test_all_types.proto" "$SRC/main/proto/cel/expr/conformance/proto3/"
cp "$CONFORMANCE/proto/cel/expr/conformance/proto2/test_all_types.proto" "$SRC/main/proto/cel/expr/conformance/proto2/" || true
mkdir -p "$SRC/main/proto/testdata/proto3" "$SRC/main/proto/protos"
cp "$CEL_JAVA/common/src/main/resources/testdata/proto3/standalone_global_enum.proto" "$SRC/main/proto/testdata/proto3/"
cp "$CEL_JAVA/testing/src/test/resources/protos/single_file.proto" "$SRC/main/proto/protos/"

# Test resources (policies).
mkdir -p "$SRC/test/resources/policy/verification" "$SRC/test/resources/conformance"
cp "$CEL_JAVA"/testing/src/test/resources/policy/verification/* "$SRC/test/resources/policy/verification/"
cp -r "$POLICY/conformance/testdata" "$SRC/test/resources/conformance/"

# Replace the Bazel runfiles helper with a classpath based one, and add the dump hook.
cp "$HERE"/harness/dev/cel/verifier/*.java "$SRC/test/java/dev/cel/verifier/"
mkdir -p "$SRC/main/java/dev/cel/verifier"
cp "$HERE"/harness/main/*.java "$SRC/main/java/dev/cel/verifier/"
python3 "$HERE/scripts/patch.py" "$SRC"
echo "synced from $(git -C "$CEL_JAVA" rev-parse HEAD)" > "$HERE/SOURCE_REVISION"

# Generate the Java protos with protoc (fetched from Maven Central).
PROTOC=$HERE/.protoc/protoc
if [ ! -x "$PROTOC" ]; then
  mkdir -p "$HERE/.protoc"
  curl -sSfL -o "$HERE/.protoc/protoc.zip" https://github.com/protocolbuffers/protobuf/releases/download/v36.2/protoc-36.2-linux-x86_64.zip
  (cd "$HERE/.protoc" && python3 -m zipfile -e protoc.zip . && mv bin/protoc protoc && chmod +x protoc)
fi
(cd "$SRC/main/proto" && "$PROTOC" -I. -I"$HERE/.protoc/include" --java_out="$SRC/main/java" $(find . -name '*.proto'))
