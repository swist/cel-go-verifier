// Package goldentest compares solver transcripts with the cel-java goldens in
// testdata/golden/java.
package goldentest

import (
	"compress/gzip"
	"io"
	"os"
	"path/filepath"

	"github.com/swist/cel-go-verifier/internal/smtdiff"
)

// Compare compares a transcript with the golden named name in dir. It returns
// found=false if there is no golden, and an empty diff if they match.
func Compare(dir, name, transcript string) (diff string, found bool, err error) {
	f, err := os.Open(filepath.Join(dir, name+".smt2.gz"))
	if err != nil {
		return "", false, nil
	}
	defer f.Close()
	zr, err := gzip.NewReader(f)
	if err != nil {
		return "", true, err
	}
	want, err := io.ReadAll(zr)
	if err != nil {
		return "", true, err
	}
	c := smtdiff.New()
	wq, err := c.Parse(string(want))
	if err != nil {
		return "", true, err
	}
	gq, err := c.Parse(transcript)
	if err != nil {
		return "", true, err
	}
	return c.Diff(wq, gq), true, nil
}
