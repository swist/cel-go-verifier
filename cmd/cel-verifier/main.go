// Command cel-verifier formally verifies CEL expressions and policies with Z3.
// It is a port of cel-java's CelVerifierTool (without the REPL).
//
// Usage:
//
//	cel-verifier check-sat    --expr EXPR [flags]
//	cel-verifier check-valid  --expr EXPR [flags]
//	cel-verifier verify-equiv --expr1 EXPR --expr2 EXPR [flags]
//	cel-verifier verify-policy --file POLICY.yaml [flags]
//
// Flags common to all commands:
//
//	--var, -v NAME:TYPE      declare a variable (repeatable), e.g. x:int, m:map<string, dyn>
//	--unknown, -u IDENT      treat an identifier as unknown (repeatable)
//	--timeout SECONDS        solver timeout (default 10)
//	--unroll-limit N         comprehension unroll limit (default 5)
//	--output_format, -fmt F  TEXT or JSON (default TEXT)
//	--backend B              proc (z3 executable, $Z3_PATH) or cgo (libz3; needs -tags z3cgo)
//
// Exit codes: 0 verified, 1 violated, 2 inconclusive, 3 error.
package main

import (
	"errors"
	"flag"
	"fmt"
	"io"
	"os"
	"path/filepath"
	"runtime/debug"
	"strings"
	"time"

	"github.com/swist/cel-go-verifier/policyverifier"
	"github.com/swist/cel-go-verifier/smt/z3proc"
	"github.com/swist/cel-go-verifier/verifier"
)

// Exit codes.
const (
	exitVerified     = 0
	exitViolated     = 1
	exitInconclusive = 2
	exitError        = 3
)

func main() { os.Exit(run(os.Args[1:], os.Stdout, os.Stderr)) }

type multiFlag []string

func (m *multiFlag) String() string     { return strings.Join(*m, ",") }
func (m *multiFlag) Set(s string) error { *m = append(*m, s); return nil }

type command struct {
	name, description string
	// strings are the command's own flags, by their names.
	strings []stringFlag
	run     func(c *invocation) int
}

type stringFlag struct {
	names       []string
	usage       string
	required    bool
	placeholder string
}

var commands = []command{
	{
		name:        "check-sat",
		description: "Verify satisfiability of a CEL expression & generate witness model",
		strings:     []stringFlag{{names: []string{"expr", "e"}, usage: "CEL expression string to verify", required: true}},
		run: func(c *invocation) int {
			return c.single(func(o options) (verifier.Result, error) {
				return checkSatisfiable(c.str("expr"), c.vars, o)
			})
		},
	},
	{
		name:        "check-valid",
		description: "Verify validity (isAlwaysTrue) of a CEL expression & generate counterexample",
		strings:     []stringFlag{{names: []string{"expr", "e"}, usage: "CEL expression string to verify", required: true}},
		run: func(c *invocation) int {
			return c.single(func(o options) (verifier.Result, error) {
				return checkValid(c.str("expr"), c.vars, o)
			})
		},
	},
	{
		name:        "verify-equiv",
		description: "Prove logical equivalence between two CEL expressions",
		strings: []stringFlag{
			{names: []string{"expr1"}, usage: "First CEL expression", required: true},
			{names: []string{"expr2"}, usage: "Second CEL expression", required: true},
		},
		run: func(c *invocation) int {
			return c.single(func(o options) (verifier.Result, error) {
				return verifyEquivalence(c.str("expr1"), c.str("expr2"), c.vars, o)
			})
		},
	},
	{
		name:        "verify-policy",
		description: "Verify policy invariants defined in a YAML policy file",
		strings:     []stringFlag{{names: []string{"file", "f"}, usage: "Path to policy YAML file", required: true}},
		run:         runVerifyPolicy,
	},
}

// invocation is a parsed command line.
type invocation struct {
	stdout, stderr io.Writer
	values         map[string]*string
	vars           []variable
	opts           options
	json           bool
}

func (c *invocation) str(name string) string { return *c.values[name] }

func (c *invocation) fail(prefix string, err error) int {
	var ce *compileError
	var ve *policyverifier.ValidationError
	var pe *policyverifier.PolicyError
	switch {
	case errors.As(err, &ce), errors.As(err, &ve):
		fmt.Fprintln(c.stderr, "Compilation error:\n"+err.Error())
	case errors.As(err, &pe):
		fmt.Fprintln(c.stderr, "Policy compilation error:\n"+err.Error())
	default:
		fmt.Fprintln(c.stderr, prefix+": "+err.Error())
	}
	return exitError
}

func (c *invocation) single(f func(options) (verifier.Result, error)) int {
	r, err := f(c.opts)
	if err != nil {
		return c.fail("Verification error", err)
	}
	if c.json {
		fmt.Fprintln(c.stdout, formatJSONResult(r))
	} else {
		fmt.Fprintln(c.stdout, formatTextResult(r))
	}
	return exitCode(r.Status)
}

func exitCode(s verifier.Status) int {
	switch s {
	case verifier.Verified:
		return exitVerified
	case verifier.Violated:
		return exitViolated
	}
	return exitInconclusive
}

func runVerifyPolicy(c *invocation) int {
	path := c.str("file")
	src, err := os.ReadFile(path)
	if errors.Is(err, os.ErrNotExist) {
		fmt.Fprintln(c.stderr, "File not found: "+path)
		return exitError
	}
	if err != nil {
		return c.fail("Policy verification error", err)
	}
	results, err := verifyPolicyInvariants(string(src), c.vars, c.opts)
	if err != nil {
		return c.fail("Policy verification error", err)
	}
	name := filepath.Base(path)
	if c.json {
		fmt.Fprintln(c.stdout, formatJSONPolicyResults(name, results))
	} else {
		fmt.Fprintln(c.stdout, formatTextPolicyResults(name, results))
	}
	return policyExitCode(results)
}

func policyExitCode(results []namedResult) int {
	code := exitVerified
	for _, r := range results {
		switch r.result.Status {
		case verifier.Violated:
			return exitViolated
		case verifier.Inconclusive:
			code = exitInconclusive
		}
	}
	return code
}

func version() string {
	if bi, ok := debug.ReadBuildInfo(); ok && bi.Main.Version != "" {
		return bi.Main.Version
	}
	return "(devel)"
}

func usage(w io.Writer) {
	fmt.Fprintln(w, "Usage: cel-verifier [--version] COMMAND [flags]")
	fmt.Fprintln(w, "\nCEL formal verification CLI.\n\nCommands:")
	for _, c := range commands {
		fmt.Fprintf(w, "  %-14s %s\n", c.name, c.description)
	}
	fmt.Fprintln(w, "\nRun 'cel-verifier COMMAND --help' for the flags of a command.")
}

func run(args []string, stdout, stderr io.Writer) int {
	if len(args) == 0 {
		usage(stderr)
		return exitError
	}
	switch args[0] {
	case "--version", "-V", "version":
		fmt.Fprintln(stdout, "cel-verifier "+version())
		return 0
	case "--help", "-h", "help":
		usage(stdout)
		return 0
	}
	var cmd *command
	for i := range commands {
		if commands[i].name == args[0] {
			cmd = &commands[i]
		}
	}
	if cmd == nil {
		fmt.Fprintf(stderr, "Unknown command '%s'.\n", args[0])
		usage(stderr)
		return exitError
	}

	fs := flag.NewFlagSet(cmd.name, flag.ContinueOnError)
	fs.SetOutput(stderr)
	c := &invocation{stdout: stdout, stderr: stderr, values: map[string]*string{}}
	for _, sf := range cmd.strings {
		v := new(string)
		for _, n := range sf.names {
			fs.StringVar(v, n, "", sf.usage)
		}
		c.values[sf.names[0]] = v
	}
	var varSpecs, unknowns multiFlag
	fs.Var(&varSpecs, "var", "Variable declaration NAME:TYPE (repeatable), e.g. x:int, tags:list<string>")
	fs.Var(&varSpecs, "v", "Shorthand for --var")
	fs.Var(&unknowns, "unknown", "Identifier to treat as unknown (repeatable)")
	fs.Var(&unknowns, "u", "Shorthand for --unknown")
	timeout := fs.Int("timeout", 10, "Solver timeout in seconds")
	unroll := fs.Int("unroll-limit", 5, "Comprehension unroll limit for BMC")
	format := new(string)
	fs.StringVar(format, "output_format", "TEXT", "Output format: TEXT or JSON")
	fs.StringVar(format, "fmt", "TEXT", "Shorthand for --output_format")
	backendName := fs.String("backend", "proc", "Solver backend: proc (z3 executable, $Z3_PATH) or cgo (libz3, needs -tags z3cgo)")
	if err := fs.Parse(args[1:]); err != nil {
		if errors.Is(err, flag.ErrHelp) {
			return 0
		}
		return exitError
	}
	if fs.NArg() > 0 {
		fmt.Fprintf(stderr, "Unexpected arguments: %s\n", strings.Join(fs.Args(), " "))
		return exitError
	}
	for _, sf := range cmd.strings {
		if sf.required && *c.values[sf.names[0]] == "" {
			fmt.Fprintf(stderr, "Missing required option: '--%s'\n", sf.names[0])
			return exitError
		}
	}

	switch strings.ToUpper(*format) {
	case "JSON":
		c.json = true
	case "TEXT":
	default:
		fmt.Fprintf(stderr, "Invalid output format '%s'. Defaulting to TEXT.\n", *format)
	}

	prefix := "Verification error"
	if cmd.name == "verify-policy" {
		prefix = "Policy verification error"
	}
	vars, err := parseVariables(varSpecs)
	if err != nil {
		return c.fail(prefix, err)
	}
	c.vars = vars
	c.opts = options{
		timeout:     time.Duration(*timeout) * time.Second,
		unrollLimit: *unroll,
		unknowns:    unknowns,
	}
	switch *backendName {
	case "proc":
		c.opts.backend = z3proc.New()
	case "cgo":
		b, err := cgoBackend()
		if err != nil {
			return c.fail(prefix, err)
		}
		c.opts.backend = b
	default:
		return c.fail(prefix, fmt.Errorf("unknown backend '%s' (want proc or cgo)", *backendName))
	}
	return cmd.run(c)
}
