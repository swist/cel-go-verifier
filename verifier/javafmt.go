package verifier

import (
	"fmt"
	"math"
	"strconv"
	"strings"
	"time"
)

// javaDoubleString formats a finite double like Java's Double.toString.
func javaDoubleString(v float64) string {
	if v == 0 {
		if math.Signbit(v) {
			return "-0.0"
		}
		return "0.0"
	}
	neg := v < 0
	if neg {
		v = -v
	}
	// Shortest decimal that round-trips: digits d1.d2d3... x 10^exp.
	e := strconv.FormatFloat(v, 'e', -1, 64)
	mant, expStr, _ := strings.Cut(e, "e")
	exp, _ := strconv.Atoi(expStr)
	digits := strings.Replace(mant, ".", "", 1)
	var s string
	if v >= 1e-3 && v < 1e7 {
		// Plain notation with at least one digit after the point.
		point := exp + 1
		switch {
		case point <= 0:
			s = "0." + strings.Repeat("0", -point) + digits
		case point >= len(digits):
			s = digits + strings.Repeat("0", point-len(digits)) + ".0"
		default:
			s = digits[:point] + "." + digits[point:]
		}
	} else {
		frac := digits[1:]
		if frac == "" {
			frac = "0"
		}
		s = digits[:1] + "." + frac + "E" + strconv.Itoa(exp)
	}
	if neg {
		return "-" + s
	}
	return s
}

// javaInstantString formats a time like java.time.Instant.toString (ISO-8601, UTC).
func javaInstantString(seconds int64, nanos int64) string {
	t := time.Unix(seconds, nanos).UTC()
	var sb strings.Builder
	sb.WriteString(fmt.Sprintf("%04d-%02d-%02dT%02d:%02d:%02d", t.Year(), int(t.Month()), t.Day(), t.Hour(), t.Minute(), t.Second()))
	if nanos != 0 {
		sb.WriteByte('.')
		sb.WriteString(formatNanos(nanos))
	}
	sb.WriteByte('Z')
	return sb.String()
}

// formatNanos uses 3, 6 or 9 digits, like ProtoTimeUtils and Instant.toString.
func formatNanos(nanos int64) string {
	switch {
	case nanos%1_000_000 == 0:
		return fmt.Sprintf("%03d", nanos/1_000_000)
	case nanos%1_000 == 0:
		return fmt.Sprintf("%06d", nanos/1_000)
	}
	return fmt.Sprintf("%09d", nanos)
}

// formatDuration formats seconds and nanos of the same sign like cel-java's ProtoTimeUtils.formatDuration.
func formatDuration(seconds, nanos int64) string {
	var sb strings.Builder
	if seconds < 0 || nanos < 0 {
		sb.WriteByte('-')
		seconds, nanos = -seconds, -nanos
	}
	sb.WriteString(strconv.FormatInt(seconds, 10))
	if nanos != 0 {
		sb.WriteByte('.')
		sb.WriteString(formatNanos(nanos))
	}
	sb.WriteByte('s')
	return sb.String()
}
