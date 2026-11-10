import P384.Bytes

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace P384

def bnExportMask (j topBytes : BitVec 64) : BitVec 64 :=
  0 - ((j - topBytes) >>> 63)

theorem sub_highBit64 (x y : BitVec 64)
    (hx : x.toNat < 2^63) (hy : y.toNat < 2^63) :
    (x - y) >>> 63 = if x.toNat < y.toNat then 1 else 0 := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  by_cases h : x.toNat < y.toNat
  · rw [if_pos h, BitVec.toNat_sub_of_lt (by simpa only [BitVec.lt_def] using h)]
    change (2^64 - (y.toNat - x.toNat)) / 2^63 = 1
    omega
  · rw [if_neg h, BitVec.toNat_sub_of_le (by simp only [BitVec.le_def]; omega)]
    change (x.toNat - y.toNat) / 2^63 = 0
    omega

theorem bnExportMask_correct (j topBytes : BitVec 64)
    (hj : j.toNat < 2^63) (ht : topBytes.toNat < 2^63) :
    bnExportMask j topBytes =
      if j.toNat < topBytes.toNat then BitVec.allOnes 64 else 0 := by
  rw [bnExportMask, sub_highBit64 j topBytes hj ht]
  split <;> decide

def bnExportAdvance (i last : BitVec 64) : BitVec 64 :=
  i + ((i - last) >>> 63)

theorem bnExportAdvance_correct (i last : BitVec 64)
    (hi : i.toNat ≤ last.toNat) (hl : last.toNat < 2^63) :
    (bnExportAdvance i last).toNat = min (i.toNat + 1) last.toNat := by
  rw [bnExportAdvance, sub_highBit64 i last (by omega) hl]
  by_cases h : i.toNat < last.toNat
  · rw [if_pos h, BitVec.toNat_add]
    change (i.toNat + 1) % 2^64 = min (i.toNat + 1) last.toNat
    rw [Nat.mod_eq_of_lt (by omega), Nat.min_eq_left (by omega)]
  · rw [if_neg h, BitVec.toNat_add]
    change (i.toNat + 0) % 2^64 = min (i.toNat + 1) last.toNat
    rw [Nat.add_zero, Nat.mod_eq_of_lt i.isLt]
    omega

def bnExportCursor (last : BitVec 64) : ℕ → BitVec 64
  | 0 => 0
  | j + 1 => bnExportAdvance (bnExportCursor last j) last

theorem bnExportCursor_correct (last : BitVec 64) (hl : last.toNat < 2^63) (j : ℕ) :
    (bnExportCursor last j).toNat = min j last.toNat := by
  induction j with
  | zero => simp [bnExportCursor]
  | succ j ih =>
      rw [bnExportCursor, bnExportAdvance_correct _ last (by rw [ih]; omega) hl, ih]
      omega

def bnPackLoop : List Byte → BitVec 64 → ℕ → BitVec 64
  | [], acc, _ => acc
  | b :: bs, acc, m => bnPackLoop bs (acc ||| (b.setWidth 64 <<< m)) (m + 8)

theorem bnPackStep (b : Byte) (acc : BitVec 64) (m : ℕ)
    (hm : m + 8 ≤ 64) (ha : acc.toNat < 2^m) :
    (acc ||| (b.setWidth 64 <<< m)).toNat = acc.toNat + 2^m * b.toNat := by
  have hb : b.toNat < 256 := b.isLt
  have hs : b.toNat * 2^m < 2^64 := by
    have hp : (2 : ℕ)^m * 256 ≤ 2^64 := by
      simpa only [pow_add, show (2 : ℕ)^8 = 256 from rfl] using
        (Nat.pow_le_pow_of_le Nat.one_lt_two hm)
    have := Nat.mul_lt_mul_of_pos_right hb (Nat.two_pow_pos m)
    omega
  rw [BitVec.toNat_or, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq,
    BitVec.toNat_setWidth, Nat.mod_eq_of_lt (show b.toNat < 2^64 by omega),
    Nat.mod_eq_of_lt hs, Nat.or_comm]
  simpa only [Nat.mul_comm, Nat.add_comm] using
    (Nat.two_pow_add_eq_or_of_lt ha b.toNat).symm

theorem bnPackLoop_correct (bs : List Byte) (acc : BitVec 64) (m : ℕ)
    (hm : m + 8 * bs.length ≤ 64) (ha : acc.toNat < 2^m) :
    (bnPackLoop bs acc m).toNat = acc.toNat + 2^m * leValue bs := by
  induction bs generalizing acc m with
  | nil => simp [bnPackLoop, leValue]
  | cons b bs ih =>
      have hm8 : m + 8 ≤ 64 := by simp only [List.length_cons] at hm; omega
      have hs := bnPackStep b acc m hm8 ha
      have hb : b.toNat < 256 := b.isLt
      have hn : (acc ||| (b.setWidth 64 <<< m)).toNat < 2^(m + 8) := by
        rw [hs, pow_add]
        norm_num
        nlinarith [Nat.two_pow_pos m]
      rw [bnPackLoop, ih _ _ (by simp only [List.length_cons] at hm; omega) hn, hs]
      simp only [leValue, pow_add]
      norm_num
      ring

def bnPack (bs : List Byte) : BitVec 64 := bnPackLoop bs 0 0

theorem bnPack_correct (bs : List Byte) (h : bs.length ≤ 8) :
    (bnPack bs).toNat = leValue bs := by
  simpa only [bnPack, show (0 : BitVec 64).toNat = 0 from rfl,
    pow_zero, one_mul, zero_add] using
    bnPackLoop_correct bs 0 0 (by omega) (by decide)

theorem bnExport_read_bound (capacity : ℕ) (hc : 0 < capacity)
    (hh : capacity * 8 < 2^63) (j : ℕ) :
    (bnExportCursor (BitVec.ofNat 64 (capacity * 8 - 1)) j).toNat / 8 < capacity := by
  have hn : (BitVec.ofNat 64 (capacity * 8 - 1)).toNat = capacity * 8 - 1 := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  rw [bnExportCursor_correct _ (by rw [hn]; omega), hn]
  omega

end P384
