package verifier

import (
	"fmt"
	"testing"
)

// Expected values computed with Guava's Hashing.farmHashFingerprint64().
func TestFarmFingerprint64MatchesGuava(t *testing.T) {
	want := map[int]string{
		0: "9ae16a3b2f90404f", 1: "57821efdee1b7472", 3: "5f043801775be181", 4: "dcf15d9b38b260fc",
		7: "545ac134b57925ff", 8: "d14693440d28f69a", 15: "c338033dfa6dca8d", 16: "d9b28ec31be83978",
		17: "ffb7cd799a150d69", 31: "61a0625587879a75", 32: "5b0213e62a3ca399", 33: "d73bbb576c6c9808",
		63: "ff2033b26af5e749", 64: "56317ec658bfa4f9", 65: "5a5b9a92eb3061d6", 100: "7f2537959ee60afd",
		128: "62d2c1879bd73de5", 129: "d8e52f1caf21aae2", 200: "8f2dac6e1bb7686d", 1000: "887fc552cf10ef81",
	}
	for n, w := range want {
		b := make([]byte, n)
		for i := range b {
			b[i] = byte(i*31 + 7)
		}
		if got := fmt.Sprintf("%x", farmFingerprint64(b)); got != w {
			t.Errorf("len %d: got %s, want %s", n, got, w)
		}
	}
}
