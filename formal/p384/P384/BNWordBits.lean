import P384.BitWidth
import P384.GeneratedBNWordBits
import P384.Words

set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 16384
set_option exponentiation.threshold 2048

namespace P384

theorem bitvec_zero_iff {w : ℕ} (x : BitVec w) : x = 0 ↔ x.toNat = 0 := by
  rw [BitVec.toNat_eq]
  rfl

theorem unsignedNonzeroMask_correct (x : BitVec 64) (hx : x.toNat < 2^63) :
    (0 : BitVec 64) - ((((0 : BitVec 64) - x) &&& BitVec.allOnes 64) >>> 63) =
      if x = 0 then 0 else BitVec.allOnes 64 := by
  rw [BitVec.and_allOnes]
  change bnExportMask 0 x = _
  rw [bnExportMask_correct _ x (by decide) hx]
  by_cases hz : x = 0
  · subst x
    decide
  · have hn : 0 < x.toNat := by
      have hne : x.toNat ≠ 0 := fun h => hz ((bitvec_zero_iff x).2 h)
      omega
    simp only [show (0 : BitVec 64).toNat = 0 from rfl, if_pos hn, if_neg hz]

theorem signExtend32_toNat (x : BitVec 32) (hx : x.toNat < 2^31) :
    (x.signExtend 64).toNat = x.toNat := by
  have hm : x.msb = false := BitVec.msb_eq_false_iff_two_mul_lt.2 (by omega)
  rw [BitVec.signExtend_eq_setWidth_of_msb_false hm, BitVec.toNat_setWidth,
    Nat.mod_eq_of_lt (by omega)]

structure BNBitState where
  limb : BitVec 64
  count : BitVec 32

def bnWordBitStep (s : BNBitState) (n : ℕ) : BNBitState :=
  let x := s.limb >>> n
  let t := ((0 : BitVec 64) - x) &&& BitVec.allOnes 64
  let mask := (0 : BitVec 64) - (t >>> 63)
  let count := ((s.count.signExtend 64) + (BitVec.ofNat 64 n &&& mask)).setWidth 32
  let limb := s.limb ^^^ ((x ^^^ s.limb) &&& mask)
  ⟨limb, count⟩

def bnWordBitRun : ℕ → BNBitState → BNBitState
  | 0, s => s
  | k + 1, s => bnWordBitRun k (bnWordBitStep s (2^k))

theorem bnWordBitStep_mask (s : BNBitState) (n : ℕ) (hn : 0 < n ∧ n ≤ 32) :
    (0 : BitVec 64) - ((((0 : BitVec 64) - (s.limb >>> n)) &&& BitVec.allOnes 64) >>> 63) =
      if s.limb.toNat / 2^n = 0 then 0 else BitVec.allOnes 64 := by
  have hs := BitVec.toNat_ushiftRight_lt s.limb n (by omega)
  have hp : (2 : ℕ)^(64 - n) ≤ 2^63 := Nat.pow_le_pow_of_le Nat.one_lt_two (by omega)
  rw [unsignedNonzeroMask_correct _ (hs.trans_le hp)]
  simp only [bitvec_zero_iff, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]

theorem bnWordBitStep_count (s : BNBitState) (n : ℕ) (hn : 0 < n ∧ n ≤ 32)
    (hb : s.count.toNat + n ≤ 128) :
    (bnWordBitStep s n).count.toNat = s.count.toNat +
      if s.limb.toNat / 2^n = 0 then 0 else n := by
  have hs := signExtend32_toNat s.count (by omega)
  have hz (x : BitVec 64) : x &&& (0 : BitVec 64) = 0 := BitVec.and_zero
  dsimp only [bnWordBitStep]
  rw [bnWordBitStep_mask s n hn]
  by_cases h : s.limb.toNat / 2^n = 0
  · simp only [if_pos h]
    rw [hz, BitVec.toNat_setWidth, BitVec.toNat_add, hs]
    change (s.count.toNat + 0) % 2^64 % 2^32 = s.count.toNat + 0
    omega
  · simp only [if_neg h]
    rw [BitVec.and_allOnes, BitVec.toNat_setWidth, BitVec.toNat_add, hs,
      BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show n < 2^64 by omega)]
    omega

theorem bnWordBitStep_limb (s : BNBitState) (n : ℕ) (hn : 0 < n ∧ n ≤ 32) :
    (bnWordBitStep s n).limb.toNat =
      if s.limb.toNat / 2^n = 0 then s.limb.toNat else s.limb.toNat / 2^n := by
  have he (x y mask : BitVec 64) : x ^^^ ((y ^^^ x) &&& mask) = copyWord x y mask := by
    rw [copyWord, BitVec.and_comm]
  dsimp only [bnWordBitStep]
  rw [bnWordBitStep_mask s n hn]
  by_cases h : s.limb.toNat / 2^n = 0
  · simp only [if_pos h]
    rw [he, copyWord_zero]
  · simp only [if_neg h]
    rw [he, copyWord_ones, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]

theorem bnWordBitRun_count (k : ℕ) (s : BNBitState) (hk : k ≤ 6)
    (hb : s.count.toNat + (2^k - 1) ≤ 128) :
    (bnWordBitRun k s).count.toNat = s.count.toNat + bitOffsets k s.limb.toNat := by
  induction k generalizing s with
  | zero => simp [bnWordBitRun, bitOffsets]
  | succ k ih =>
      have hp : 0 < (2 : ℕ)^k ∧ (2 : ℕ)^k ≤ 32 :=
        ⟨Nat.two_pow_pos k, (Nat.pow_le_pow_of_le Nat.one_lt_two (show k ≤ 5 by omega))⟩
      have hstep := bnWordBitStep_count s (2^k) hp (by
        have hpos := Nat.two_pow_pos k
        rw [pow_succ] at hb
        omega)
      have hbudget : (bnWordBitStep s (2^k)).count.toNat + (2^k - 1) ≤ 128 := by
        rw [hstep]
        have hpos := Nat.two_pow_pos k
        rw [pow_succ] at hb
        split <;> omega
      rw [bnWordBitRun, ih _ (by omega) hbudget, hstep, bnWordBitStep_limb s (2^k) hp]
      by_cases hz : s.limb.toNat / 2^(2^k) = 0 <;> simp only [bitOffsets, hz, ↓reduceIte] <;> omega

theorem machineBNNumBitsWord_run (x : BitVec 64) :
    machineBNNumBitsWord x = (bnWordBitRun 6 ⟨x, if x = 0 then 0 else 1⟩).count := by
  rfl

theorem machineBNNumBitsWord_correct (x : BitVec 64) :
    (machineBNNumBitsWord x).toNat = x.toNat.size := by
  rw [machineBNNumBitsWord_run]
  have hb : (if x = 0 then (0 : BitVec 32) else 1).toNat ≤ 1 := by split <;> decide
  rw [bnWordBitRun_count 6 _ (by decide) (by norm_num; omega)]
  have hi := bitOffsets_correct 6 x.toNat x.isLt
  by_cases hz : x = 0
  · subst x
    simpa only [↓reduceIte, show (0 : BitVec 32).toNat = 0 from rfl,
      show (0 : BitVec 64).toNat = 0 from rfl] using hi
  · have hn : x.toNat ≠ 0 := fun h => hz ((bitvec_zero_iff x).2 h)
    simpa only [if_neg hz, if_neg hn, show (1 : BitVec 32).toNat = 1 from rfl] using hi

theorem machineBNNumBitsWord_range (x : BitVec 64) : (machineBNNumBitsWord x).toNat ≤ 64 := by
  rw [machineBNNumBitsWord_correct]
  exact Nat.size_le.2 x.isLt

def bnWordBitCounters : ℕ → BNBitState → List (BitVec 32)
  | 0, s => [s.count]
  | k + 1, s => s.count :: bnWordBitCounters k (bnWordBitStep s (2^k))

theorem bnWordBitStep_budget (k : ℕ) (s : BNBitState) (hk : k < 6)
    (hb : s.count.toNat + (2^(k + 1) - 1) ≤ 128) :
    (bnWordBitStep s (2^k)).count.toNat + (2^k - 1) ≤ 128 := by
  have hp : 0 < (2 : ℕ)^k ∧ (2 : ℕ)^k ≤ 32 :=
    ⟨Nat.two_pow_pos _, Nat.pow_le_pow_of_le Nat.one_lt_two (show k ≤ 5 by omega)⟩
  have hs := bnWordBitStep_count s (2^k) hp (by rw [pow_succ] at hb; omega)
  rw [hs]
  rw [pow_succ] at hb
  split <;> omega

theorem bnWordBitCounters_bound (k : ℕ) (s : BNBitState) (hk : k ≤ 6)
    (hb : s.count.toNat + (2^k - 1) ≤ 128) :
    ∀ b ∈ bnWordBitCounters k s, b.toNat ≤ 128 := by
  induction k generalizing s with
  | zero => simp [bnWordBitCounters] at *; assumption
  | succ k ih =>
      intro b hm
      simp only [bnWordBitCounters, List.mem_cons] at hm
      rcases hm with rfl | hm
      · omega
      · exact ih _ (by omega) (bnWordBitStep_budget k s (by omega) hb) b hm

theorem machineBNWordBits_counters_signed (x : BitVec 64) :
    ∀ b ∈ (machineBNWordBitsTrace x).counters,
      b.toNat ≤ 128 ∧ b.toInt = (b.toNat : ℤ) := by
  have he : (machineBNWordBitsTrace x).counters =
      bnWordBitCounters 6 ⟨x, if x = 0 then 0 else 1⟩ := by rfl
  rw [he]
  intro b hm
  have hi : (if x = 0 then (0 : BitVec 32) else 1).toNat ≤ 1 := by split <;> decide
  have hb := bnWordBitCounters_bound 6 ⟨x, if x = 0 then 0 else 1⟩
    (by decide) (by norm_num; omega) b hm
  exact ⟨hb, BitVec.toInt_eq_toNat_of_lt (by omega)⟩

end P384
