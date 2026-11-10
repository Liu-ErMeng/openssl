import P384.WordSemantics

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option exponentiation.threshold 2048

namespace P384

def Signed64 (x : ℤ) : Prop := -2^63 ≤ x ∧ x < 2^63

theorem signed_ofInt_exact (x : ℤ) (hx : Signed64 x) :
    (BitVec.ofInt 64 x).toInt = x :=
  BitVec.toInt_ofInt_eq_self (by decide) hx.1 hx.2

theorem ofInt_sshiftRight (x : ℤ) (hx : Signed64 x) (n : ℕ) :
    (BitVec.ofInt 64 x).sshiftRight n = BitVec.ofInt 64 (x / 2^n) := by
  simp only [BitVec.sshiftRight, signed_ofInt_exact x hx, Int.shiftRight_eq_div_pow]
  congr 1
  norm_cast

theorem ofInt_mask_any (x : ℤ) (n : ℕ) (hn : n ≤ 64) :
    BitVec.ofInt 64 x &&& BitVec.ofNat 64 (2^n - 1) = BitVec.ofInt 64 (x % 2^n) := by
  apply eq_of_unsigned_eq
  have hp : (0 : ℤ) < 2^n := by positivity
  have hle : (2 : ℤ)^n ≤ 2^64 := by exact_mod_cast Nat.pow_le_pow_of_le Nat.one_lt_two hn
  have hd : (2 : ℤ)^n ∣ 2^64 := pow_dvd_pow 2 hn
  rw [unsigned_mask _ n hn, unsigned_ofInt, unsigned_ofInt,
    Int.emod_emod_of_dvd _ hd,
    Int.emod_eq_of_lt (Int.emod_nonneg _ (ne_of_gt hp))
      ((Int.emod_lt_of_pos _ hp).trans_le hle)]

theorem borrow_shift63 (x : ℤ) (hx : -2^32 ≤ x ∧ x < 2^56) :
    (BitVec.ofInt 64 x).sshiftRight 63 = BitVec.ofInt 64 (x / radix) := by
  rw [ofInt_sshiftRight x (by unfold Signed64; norm_num at hx ⊢; omega)]
  congr 1
  norm_num [radix] at hx ⊢
  omega

theorem borrow_mask (x : ℤ) (hx : x = -1 ∨ x = 0) (n : ℕ) :
    (BitVec.ofInt 64 x &&& BitVec.ofNat 64 (2^n)) = BitVec.ofInt 64 (-x * 2^n) := by
  rcases hx with rfl | rfl
  · have hp : BitVec.ofInt 64 ((2 : ℤ)^n) = BitVec.ofNat 64 ((2 : ℕ)^n) := by
      have hc : (2 : ℤ)^n = ((2^n : ℕ) : ℤ) := by norm_cast
      rw [hc, BitVec.ofInt_natCast]
    simpa only [neg_neg, one_mul, BitVec.ofInt_neg] using
      (show BitVec.ofInt 64 (-1) &&& BitVec.ofNat 64 (2^n) =
        BitVec.ofInt 64 ((2 : ℤ)^n) by rw [hp]; exact BitVec.allOnes_and)
  · simp

end P384
