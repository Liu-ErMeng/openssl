import P384.WordSemantics

set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace P384

def constantTimeMsb32 (x : BitVec 32) : BitVec 32 := 0 - (x >>> 31)
def constantTimeIsZero32 (x : BitVec 32) : BitVec 32 := constantTimeMsb32 (~~~x &&& (x - 1))
def constantTimeEq32 (a b : BitVec 32) : BitVec 32 := constantTimeIsZero32 (a ^^^ b)

theorem constantTimeIsZero32_correct (x : BitVec 32) :
    constantTimeIsZero32 x = if x = 0 then BitVec.allOnes 32 else 0 := by
  by_cases hz : x = 0
  · subst x
    decide
  · have hx := x.isLt
    have hp : 0 < x.toNat := by
      have hn : x.toNat ≠ 0 := fun h => hz (BitVec.eq_of_toNat_eq h)
      omega
    have hsmall : (~~~x &&& (x - 1)).toNat < 2^31 := by
      by_cases hh : x.toNat < 2^31
      · have hs : (x - 1).toNat = x.toNat - 1 := by
          rw [BitVec.toNat_sub]
          change (2^32 - 1 + x.toNat) % 2^32 = x.toNat - 1
          omega
        have hle : (~~~x &&& (x - 1)).toNat ≤ (x - 1).toNat := by
          rw [BitVec.toNat_and]
          exact Nat.and_le_right
        rw [hs] at hle
        omega
      · have hle : (~~~x &&& (x - 1)).toNat ≤ (~~~x).toNat := by
          rw [BitVec.toNat_and]
          exact Nat.and_le_left
        rw [BitVec.toNat_not] at hle
        omega
    have hs : (~~~x &&& (x - 1)) >>> 31 = (0 : BitVec 32) := by
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
      exact Nat.div_eq_of_lt hsmall
    unfold constantTimeIsZero32 constantTimeMsb32
    rw [hs, if_neg hz]
    decide

theorem constantTimeEq32_correct (a b : BitVec 32) :
    constantTimeEq32 a b = if a = b then BitVec.allOnes 32 else 0 := by
  have hz : a ^^^ b = (0 : BitVec 32) ↔ a = b := BitVec.xor_eq_zero_iff
  simp only [constantTimeEq32, constantTimeIsZero32_correct, hz]

theorem eq32_top_index (top j : ℕ) (ht : top < 2^31) (hj : j < 2^31) :
    BitVec.ofInt 32 ((top : ℤ) - 1) = BitVec.ofNat 32 j ↔ top = j + 1 := by
  cases top with
  | zero =>
      rw [BitVec.toNat_eq, BitVec.toNat_ofNat]
      change 2^32 - 1 = j % 2^32 ↔ (0 : ℕ) = j + 1
      rw [Nat.mod_eq_of_lt (by omega)]
      omega
  | succ n =>
      have hc : ((n + 1 : ℕ) : ℤ) - 1 = (n : ℤ) := by omega
      rw [hc, BitVec.ofInt_natCast, BitVec.toNat_eq, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt (show n < 2^32 by omega), Nat.mod_eq_of_lt (show j < 2^32 by omega)]
      omega

theorem constantTimeEq32_top_index (top j : ℕ) (ht : top < 2^31) (hj : j < 2^31) :
    constantTimeEq32 (BitVec.ofInt 32 ((top : ℤ) - 1)) (BitVec.ofNat 32 j) =
      if top = j + 1 then BitVec.allOnes 32 else 0 := by
  simp only [constantTimeEq32_correct, eq32_top_index top j ht hj]

theorem constantTimeEq32_top_zero (top : ℕ) (ht : top < 2^31) :
    ~~~constantTimeEq32 (BitVec.ofInt 32 ((top : ℤ) - 1)) (BitVec.ofInt 32 (-1)) =
      if top = 0 then 0 else BitVec.allOnes 32 := by
  have he : BitVec.ofInt 32 ((top : ℤ) - 1) = BitVec.ofInt 32 (-1) ↔ top = 0 := by
    cases top with
    | zero => simp
    | succ n =>
        have hc : ((n + 1 : ℕ) : ℤ) - 1 = (n : ℤ) := by omega
        rw [hc, BitVec.toNat_eq, BitVec.ofInt_natCast, BitVec.toNat_ofNat]
        change n % 2^32 = 2^32 - 1 ↔ (n + 1 : ℕ) = 0
        rw [Nat.mod_eq_of_lt (by omega)]
        omega
  rw [constantTimeEq32_correct]
  simp only [he]
  by_cases hz : top = 0
  · simp only [if_pos hz]
    decide
  · simp only [if_neg hz]
    decide

end P384
