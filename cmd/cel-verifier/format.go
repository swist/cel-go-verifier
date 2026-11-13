package main

import (
	"fmt"
	"strings"

	"github.com/swist/cel-go-verifier/verifier"
)

const (
	ansiReset  = "\x1b[0m"
	ansiBold   = "\x1b[1m"
	ansiGreen  = "\x1b[32m"
	ansiRed    = "\x1b[31m"
	ansiYellow = "\x1b[33m"
)

// namedResult is the result of one invariant.
type namedResult struct {
	id     string
	result verifier.Result
}

func statusColor(s verifier.Status) string {
	switch s {
	case verifier.Verified:
		return ansiGreen
	case verifier.Violated:
		return ansiRed
	}
	return ansiYellow
}

func formatTextResult(r verifier.Result) string {
	var b strings.Builder
	fmt.Fprintf(&b, "%s%s[%s]%s", statusColor(r.Status), ansiBold, r.Status, ansiReset)
	if m := r.Message(); m != "" {
		b.WriteString(" " + m)
	}
	return b.String()
}

func formatTextPolicyResults(policyName string, results []namedResult) string {
	var b strings.Builder
	fmt.Fprintf(&b, "%sPolicy Invariant Verification for '%s':\n%s", ansiBold, policyName, ansiReset)
	for _, nr := range results {
		symbol := "✗"
		if nr.result.Status == verifier.Verified {
			symbol = "✓"
		}
		fmt.Fprintf(&b, "  %s%s Invariant '%s': %s%s", statusColor(nr.result.Status), symbol, nr.id, nr.result.Status, ansiReset)
		if m := nr.result.Message(); m != "" {
			b.WriteString("\n    " + strings.ReplaceAll(m, "\n", "\n    "))
		}
		b.WriteString("\n")
	}
	return strings.TrimSpace(b.String())
}

func formatJSONResult(r verifier.Result) string {
	return fmt.Sprintf("{\n  \"status\": \"%s\",\n  \"message\": \"%s\"\n}", r.Status, escapeJSON(r.Message()))
}

func formatJSONPolicyResults(policyName string, results []namedResult) string {
	var b strings.Builder
	fmt.Fprintf(&b, "{\n  \"policyName\": \"%s\",\n  \"invariants\": [\n", escapeJSON(policyName))
	for i, nr := range results {
		b.WriteString("    {\n")
		fmt.Fprintf(&b, "      \"id\": \"%s\",\n", escapeJSON(nr.id))
		fmt.Fprintf(&b, "      \"status\": \"%s\",\n", nr.result.Status)
		fmt.Fprintf(&b, "      \"message\": \"%s\"\n", escapeJSON(nr.result.Message()))
		b.WriteString("    }")
		if i < len(results)-1 {
			b.WriteString(",")
		}
		b.WriteString("\n")
	}
	b.WriteString("  ]\n}")
	return b.String()
}

// escapeJSON escapes a string for a JSON string literal, like cel-java's FormatUtils.
func escapeJSON(s string) string {
	var b strings.Builder
	for _, c := range s {
		switch c {
		case '\\':
			b.WriteString(`\\`)
		case '"':
			b.WriteString(`\"`)
		case '\b':
			b.WriteString(`\b`)
		case '\f':
			b.WriteString(`\f`)
		case '\n':
			b.WriteString(`\n`)
		case '\r':
			b.WriteString(`\r`)
		case '\t':
			b.WriteString(`\t`)
		default:
			if c < 0x20 {
				fmt.Fprintf(&b, `\u%04x`, c)
			} else {
				b.WriteRune(c)
			}
		}
	}
	return b.String()
}
