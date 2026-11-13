package verifier

import (
	"encoding/binary"
	"math/bits"
)

// farmFingerprint64 is FarmHash's Fingerprint64 (farmhashna::Hash64), as
// implemented by Guava's Hashing.farmHashFingerprint64().
func farmFingerprint64(b []byte) uint64 {
	n := len(b)
	switch {
	case n <= 16:
		return farmLen0to16(b)
	case n <= 32:
		return farmLen17to32(b)
	case n <= 64:
		return farmLen33to64(b)
	}
	return farmLen65Plus(b)
}

const (
	fk0 uint64 = 0xc3a5c85c97cb3127
	fk1 uint64 = 0xb492b66fbe98f273
	fk2 uint64 = 0x9ae16a3b2f90404f
)

func load64(b []byte, i int) uint64 { return binary.LittleEndian.Uint64(b[i:]) }
func load32(b []byte, i int) uint64 { return uint64(binary.LittleEndian.Uint32(b[i:])) }
func ror(v uint64, s int) uint64    { return bits.RotateLeft64(v, -s) }
func shiftMix(v uint64) uint64      { return v ^ (v >> 47) }

func hashLen16(u, v, mul uint64) uint64 {
	a := (u ^ v) * mul
	a ^= a >> 47
	b := (v ^ a) * mul
	b ^= b >> 47
	return b * mul
}

func farmLen0to16(b []byte) uint64 {
	n := len(b)
	if n >= 8 {
		mul := fk2 + uint64(n)*2
		a := load64(b, 0) + fk2
		bb := load64(b, n-8)
		c := ror(bb, 37)*mul + a
		d := (ror(a, 25) + bb) * mul
		return hashLen16(c, d, mul)
	}
	if n >= 4 {
		mul := fk2 + uint64(n)*2
		a := load32(b, 0)
		return hashLen16(uint64(n)+(a<<3), load32(b, n-4), mul)
	}
	if n > 0 {
		a, bb, c := b[0], b[n>>1], b[n-1]
		y := uint32(a) + uint32(bb)<<8
		z := uint32(n) + uint32(c)<<2
		return shiftMix(uint64(y)*fk2^uint64(z)*fk0) * fk2
	}
	return fk2
}

func farmLen17to32(b []byte) uint64 {
	n := len(b)
	mul := fk2 + uint64(n)*2
	a := load64(b, 0) * fk1
	bb := load64(b, 8)
	c := load64(b, n-8) * mul
	d := load64(b, n-16) * fk2
	return hashLen16(ror(a+bb, 43)+ror(c, 30)+d, a+ror(bb+fk2, 18)+c, mul)
}

func farmLen33to64(b []byte) uint64 {
	n := len(b)
	mul := fk2 + uint64(n)*2
	a := load64(b, 0) * fk2
	bb := load64(b, 8)
	c := load64(b, n-8) * mul
	d := load64(b, n-16) * fk2
	y := ror(a+bb, 43) + ror(c, 30) + d
	z := hashLen16(y, a+ror(bb+fk2, 18)+c, mul)
	e := load64(b, 16) * mul
	f := load64(b, 24)
	g := (y + load64(b, n-32)) * mul
	h := (z + load64(b, n-24)) * mul
	return hashLen16(ror(e+f, 43)+ror(g, 30)+h, e+ror(f+a, 18)+g, mul)
}

func weakHash32Seeds(b []byte, off int, a, bb uint64) (uint64, uint64) {
	p1, p2, p3, p4 := load64(b, off), load64(b, off+8), load64(b, off+16), load64(b, off+24)
	a += p1
	bb = ror(bb+a+p4, 21)
	c := a
	a += p2
	a += p3
	bb += ror(a, 44)
	return a + p4, bb + c
}

func farmLen65Plus(b []byte) uint64 {
	n := len(b)
	var seed uint64 = 81
	x := seed
	y := seed*fk1 + 113
	z := shiftMix(y*fk2+113) * fk2
	var v0, v1, w0, w1 uint64
	x = x*fk2 + load64(b, 0)
	off := 0
	end := ((n - 1) / 64) * 64
	last64 := end + ((n - 1) & 63) - 63
	for {
		x = ror(x+y+v0+load64(b, off+8), 37) * fk1
		y = ror(y+v1+load64(b, off+48), 42) * fk1
		x ^= w1
		y += v0 + load64(b, off+40)
		z = ror(z+w0, 33) * fk1
		v0, v1 = weakHash32Seeds(b, off, v1*fk1, x+w0)
		w0, w1 = weakHash32Seeds(b, off+32, z+w1, y+load64(b, off+16))
		x, z = z, x
		off += 64
		if off == end {
			break
		}
	}
	mul := fk1 + ((z & 0xff) << 1)
	off = last64
	w0 += uint64((n - 1) & 63)
	v0 += w0
	w0 += v0
	x = ror(x+y+v0+load64(b, off+8), 37) * mul
	y = ror(y+v1+load64(b, off+48), 42) * mul
	x ^= w1 * 9
	y += v0*9 + load64(b, off+40)
	z = ror(z+w0, 33) * mul
	v0, v1 = weakHash32Seeds(b, off, v1*mul, x+w0)
	w0, w1 = weakHash32Seeds(b, off+32, z+w1, y+load64(b, off+16))
	return hashLen16(hashLen16(v0, w0, mul)+shiftMix(y)*fk0+x, hashLen16(v1, w1, mul)+z, mul)
}
