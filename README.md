# cel-go-verifier

A Go port of [cel-java's verifier](https://github.com/google/cel-java/tree/main/verifier)
(revision `a9543227488d1eb62e04c5c39f7793698e76d9dd`). It proves properties of
[CEL](https://cel.dev) expressions and policies with Z3, and finds counterexamples:

- satisfiability (`IsSatisfiable`) and validity (`IsAlwaysTrue`) of an expression,
- equivalence of two expressions (`VerifyEquivalence`),
- implications under bound symbols (`VerifyImplication`),
- equivalence and invariants of [CEL policies](https://github.com/cel-expr/cel-policy)
  (`policyverifier`),
- a CLI with the same commands as cel-java's tool, except the REPL.

It also adds theories for the Kubernetes CEL libraries (package `kube`).

The port aims to translate exactly like cel-java. For every test in cel-java's
verifier test suite, the Go port sends Z3 the same queries, compared against
transcripts recorded from cel-java.

## Layout

| Path | Contents |
| --- | --- |
| `verifier/` | The verifier: CEL → SMT translation, axioms, BMC unrolling of comprehensions, search, counterexamples, canonicalization |
| `policyverifier/` | Policy equivalence and `verification:` invariants (cel-go's policy compiler) |
| `cmd/cel-verifier/` | CLI: `check-sat`, `check-valid`, `verify-equiv`, `verify-policy` |
| `kube/` | Axioms for `k8s.io/apiserver/pkg/cel/library` |
| `smt/` | Hash-consed SMT terms mirroring the Z3 API, an SMT-LIB printer and parser |
| `smt/z3proc/` | Backend that drives the `z3` executable over SMT-LIB (default) |
| `smt/z3cgo/` | Backend on libz3 through cgo (`-tags z3cgo`) |
| `internal/smtdiff/` | Transcript recorder and canonicalizing comparator |
| `javaref/` | Maven harness that runs cel-java's tests and records their Z3 transcripts |
| `testdata/golden/` | The recorded transcripts (gzipped), axiom declarations and test-case tables |

## Requirements

- Go 1.27 (required by `k8s.io/apiserver` v0.38).
- Z3 4.14.1 (the version the goldens were recorded with):
  - the default backend runs `z3` from `$Z3_PATH` or `PATH`;
  - the cgo backend needs libz3 and its headers:
    ```bash
    CGO_CFLAGS=-I/opt/z3/include CGO_LDFLAGS=-L/opt/z3/lib LD_LIBRARY_PATH=/opt/z3/lib go test -tags z3cgo ./verifier/
    ```

Tests that need Z3 skip when it isn't found.

## Usage

```go
env, _ := cel.NewEnv(cel.Variable("x", cel.IntType))
v, _ := verifier.New(env, verifier.Timeout(5*time.Second))
a, _ := env.Compile("x > 10")
b, _ := env.Compile("10 < x")
r, _ := v.VerifyEquivalence(a, b)
fmt.Println(r.Status, r.Message()) // VERIFIED
```

Options: `Timeout`, `ComprehensionUnrollLimit` (default 5), `UnknownIdentifiers`,
`Types` (a `TypeProvider` for messages; `NewProtoTypeProvider` covers protos),
`FunctionAxioms` (custom functions), `Backend`, `Recorder`, and hooks for
extension libraries (`MessageFormatters`, `ObjectConstraints`).

A result is `VERIFIED`, `VIOLATED` (with a concrete counterexample in
`Result.Witness`), or `INCONCLUSIVE`. Inconclusive means a counterexample may
exist, but it depends on something the verifier models only approximately,
and the message says what.

### CLI

```bash
go run ./cmd/cel-verifier check-valid --expr "x > 0" --var x:int
```

```bash
go run ./cmd/cel-verifier verify-policy --file policy.yaml --var port:int -fmt json
```

Flags: `--var/-v name:type` (repeatable; `int`, `uint`, `string`, `bool`,
`double`, `bytes`, `dyn`, `timestamp`, `duration`, `list<T>`, `map<K, V>`,
`optional<T>`, and the protobuf well-known types), `--unknown/-u`, `--timeout`
(seconds), `--unroll-limit`, `--output_format/-fmt TEXT|JSON`, `--backend proc|cgo`.
Exit codes: 0 verified, 1 violated, 2 inconclusive, 3 error.

### Kubernetes libraries

```go
env, _ := cel.NewEnv(append(kube.EnvOptions(), cel.Variable("s", cel.StringType))...)
v, _ := verifier.New(env, kube.VerifierOptions()...)
a, _ := env.Compile("!isIP(s) || !cidr('10.1.0.0/16').containsIP(s) || cidr('10.0.0.0/8').containsIP(s)")
r, _ := v.IsAlwaysTrue(a) // VERIFIED
```

| Library | Model |
| --- | --- |
| Quantity | Value in nano units (`quantity('1') == quantity('1000m')`). Order, `sign`, and `add`/`sub` are exact. `isInteger`, `asInteger` and `asApproximateFloat` depend on how a quantity is written (`1000m` isn't an integer), so they're exact for constants only |
| Lists (`isSorted`, `sum`, `min`, `max`, `indexOf`, `lastIndexOf`) | Exact up to 5 elements, the unroll limit. Longer lists, NaNs and mixed numeric kinds leave the result unconstrained (approximate) |
| IP / CIDR | Family and address as an integer (plus the prefix length). Equality, family, address classes (`isLoopback`, `isGlobalUnicast`, ...), `containsIP`/`containsCIDR`, `masked`, `prefixLength` and `ip` are exact |
| Semver | Major/minor/patch and pre-release. Equality and order are exact, except the order of two different pre-releases of the same version |
| Format | `format.<name>()` and `format.named` are exact; `validate` is uninterpreted |
| Authorizer | Uninterpreted: the same check has the same outcome, and nothing else is assumed |

Conversions from constant strings (`quantity('1Gi')`, `cidr('10.0.0.0/8')`, ...)
are evaluated by the Kubernetes libraries themselves. Conversions from other
strings are uninterpreted but consistent: `isIP(s)` holds exactly when `ip(s)`
doesn't fail. Counterexamples that depend on them are inconclusive.

Variables of the libraries' types (e.g. `net.IP`) get valid representations,
and their counterexamples display as `ip('10.0.40.210')`. The tests replay
such counterexamples through the Kubernetes runtime.

## Correspondence with cel-java

`javaref/` builds cel-java's verifier sources against the published `dev.cel`
jars. A test listener writes every Z3 interaction to
`testdata/golden/java/<TestClass>.<test>.smt2.gz`. The Go tests record their own
interactions in the same format. `internal/smtdiff` canonicalizes both
transcripts and compares them query by query, assertion by assertion. Before
comparing, it expands `let`s, flattens associative operators as Z3's printer
does, and normalizes literals and string aliases.

| Test class | Transcripts | Match |
| --- | --- | --- |
| `CelVerifierZ3ImplTest` | 1220 | 1216 with the cgo backend, 1213 with the process backend |
| `CelVerifierToolTest`, `FormatUtilsTest` | 29 + 5 | all that the Go tests produce |
| `CelPolicyVerifierImplTest` | 33 compared | 19 (outcomes all match) |
| `CanonicalizationOptimizerTest` | 184 cases | all (no solver; trees compared) |

Divergences, each documented in the tests:

- **cel-go's environment differs from cel-java's (4 cases).** cel-go's stdlib
  has `int(duration)`. Its checker types `dyn_var.value()` and the
  `optional_type` identifier differently.
- **Z3's simplifier orders arguments by term creation (3 cases, process backend
  only).** The cgo backend creates terms in the same order as cel-java and
  matches.
- **Policy composition.** cel-go's policy compiler composes rules with
  `cel.@block`, which yields different (equivalent) expressions for policies
  with several matches. Set `STRICT_POLICY_GOLDEN=1` to compare these
  transcripts anyway.
- **Canonicalization text.** For rewritten `exists`/`all` macros, cel-java's
  expected text is the unparse of a stale macro call and shows only the
  predicate. The test compares the comprehension's predicate instead.

cel-java's verifier tests also compare against a runtime oracle. 15 of them
fail in the Java harness because the published 0.15.0 runtime predates the
verifier. Their transcripts are unaffected.

### Regenerating the goldens

```bash
javaref/scripts/sync.sh <cel-java checkout> <cel-conformance checkout> <cel-policy checkout>
```

```bash
cd javaref && mvn -q test
```

`sync.sh` copies the verifier sources, tests and their inputs, drops the REPL,
and patches in the dump hooks (`scripts/patch.py`). It also fetches `protoc`.
The checkouts are github.com/google/cel-java, github.com/cel-expr/cel-conformance
and github.com/cel-expr/cel-policy.
The listener writes the transcripts to `testdata/golden/java`; gzip them. Then
record the cel-java revision in `javaref/SOURCE_REVISION`.

### Running the comparison

```bash
Z3_PATH=/opt/z3/bin/z3 go test ./...
```

```bash
go test ./verifier/ -dump_transcripts=/tmp/out
```

`-dump_transcripts` writes each Go transcript, and for mismatches pretty renders
of the Java and Go queries (`.want.txt`, `.got.txt`). `-strict_golden=false` reports mismatches without failing.
