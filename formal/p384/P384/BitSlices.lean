import P384.WordSemantics

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option exponentiation.threshold 2048

namespace P384

theorem or_not_eq_ones {w : ℕ} (x m : BitVec w) :
    x ||| ~~~m = BitVec.allOnes w ↔ x &&& m = m := by
  constructor
  · intro h
    ext i hi
    have hb := BitVec.eq_of_getElem_eq_iff.mp h i hi
    simp only [BitVec.getElem_or, BitVec.getElem_not, BitVec.getElem_allOnes] at hb
    simp only [BitVec.getElem_and]
    cases hx : x[i] <;> cases hm : m[i] <;> simp_all
  · intro h
    ext i hi
    have hb := BitVec.eq_of_getElem_eq_iff.mp h i hi
    simp only [BitVec.getElem_and] at hb
    simp only [BitVec.getElem_or, BitVec.getElem_not, BitVec.getElem_allOnes]
    cases hx : x[i] <;> cases hm : m[i] <;> simp_all

theorem and_not_eq_zero {w : ℕ} (x m : BitVec w) :
    x &&& ~~~m = 0 ↔ x &&& m = x := by
  constructor
  · intro h
    ext i hi
    have hb := BitVec.eq_of_getElem_eq_iff.mp h i hi
    simp only [BitVec.getElem_and, BitVec.getElem_not, BitVec.getElem_zero] at hb
    simp only [BitVec.getElem_and]
    cases hx : x[i] <;> cases hm : m[i] <;> simp_all
  · intro h
    ext i hi
    have hb := BitVec.eq_of_getElem_eq_iff.mp h i hi
    simp only [BitVec.getElem_and] at hb
    simp only [BitVec.getElem_and, BitVec.getElem_not, BitVec.getElem_zero]
    cases hx : x[i] <;> cases hm : m[i] <;> simp_all

theorem lowMask_toNat {w : ℕ} (x : BitVec w) (k : ℕ) (hk : k ≤ w) :
    (x &&& BitVec.ofNat w (2^k - 1)).toNat = x.toNat % 2^k := by
  have hp : 0 < (2 : ℕ)^k := Nat.two_pow_pos _
  have hle := Nat.pow_le_pow_of_le Nat.one_lt_two hk
  rw [BitVec.toNat_and, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega),
    Nat.and_two_pow_sub_one_eq_mod]

theorem or_not_lowMask_ones {w : ℕ} (x : BitVec w) (k : ℕ) (hk : k ≤ w) :
    x ||| ~~~BitVec.ofNat w (2^k - 1) = BitVec.allOnes w ↔ x.toNat % 2^k = 2^k - 1 := by
  rw [or_not_eq_ones, BitVec.toNat_eq, lowMask_toNat x k hk, BitVec.toNat_ofNat]
  have hp := Nat.two_pow_pos k
  have hle := Nat.pow_le_pow_of_le Nat.one_lt_two hk
  rw [Nat.mod_eq_of_lt (show 2^k - 1 < 2^w by omega)]

theorem and_not_lowMask_zero {w : ℕ} (x : BitVec w) (k : ℕ) (hk : k ≤ w) :
    x &&& ~~~BitVec.ofNat w (2^k - 1) = 0 ↔ x.toNat / 2^k = 0 := by
  rw [and_not_eq_zero, BitVec.toNat_eq, lowMask_toNat x k hk]
  exact (Nat.mod_eq_iff_lt (ne_of_gt (Nat.two_pow_pos _))).trans
    (Nat.div_eq_zero_iff_lt (Nat.two_pow_pos _)).symm

theorem nat_or_lowMask (x k : ℕ) :
    x ||| (2^k - 1) = 2^k * (x / 2^k) + (2^k - 1) := by
  have hp := Nat.two_pow_pos k
  have hr : x % 2^k ||| (2^k - 1) = 2^k - 1 := by
    have hl := Nat.or_lt_two_pow (Nat.mod_lt x hp) (show 2^k - 1 < 2^k by omega)
    have hle : 2^k - 1 ≤ x % 2^k ||| (2^k - 1) := Nat.right_le_or
    omega
  have hm : (2^k - 1) % 2^k = 2^k - 1 := Nat.mod_eq_of_lt (by omega)
  have hd : (2^k - 1) / 2^k = 0 := Nat.div_eq_of_lt (by omega)
  calc
    _ = (x ||| (2^k - 1)) % 2^k + 2^k * ((x ||| (2^k - 1)) / 2^k) :=
      (Nat.mod_add_div _ _).symm
    _ = (2^k - 1) + 2^k * (x / 2^k) := by
      rw [Nat.or_mod_two_pow, hm, hr, Nat.or_div_two_pow, hd, Nat.or_zero]
    _ = _ := Nat.add_comm _ _

theorem or_low17_ones (x : BitVec 56) :
    x ||| (131071 : BitVec 56) = BitVec.allOnes 56 ↔ x.toNat / 2^17 = 2^39 - 1 := by
  rw [BitVec.toNat_eq, BitVec.toNat_or, BitVec.toNat_allOnes]
  change x.toNat ||| (2^17 - 1) = 2^56 - 1 ↔ _
  rw [nat_or_lowMask]
  norm_num
  omega

theorem or_low40_ones (x : BitVec 56) :
    x ||| (1099511627775 : BitVec 56) = BitVec.allOnes 56 ↔ x.toNat / 2^40 = 2^16 - 1 := by
  rw [BitVec.toNat_eq, BitVec.toNat_or, BitVec.toNat_allOnes]
  change x.toNat ||| (2^40 - 1) = 2^56 - 1 ↔ _
  rw [nat_or_lowMask]
  norm_num
  omega

theorem or_not_bit16_ones (x : BitVec 56) :
    x ||| ~~~(65536 : BitVec 56) = BitVec.allOnes 56 ↔ x.toNat / 2^16 % 2 = 1 := by
  rw [or_not_eq_ones]
  change x &&& BitVec.twoPow 56 16 = BitVec.twoPow 56 16 ↔ _
  rw [BitVec.and_twoPow]
  have hb : x.getLsbD 16 = decide (x.toNat / 2^16 % 2 = 1) := Nat.testBit_to_div_mod
  rw [hb]
  split <;> simp_all
  decide

theorem succ56_zero (x : BitVec 56) : x + 1 = 0 ↔ x = BitVec.allOnes 56 := by
  rw [BitVec.toNat_eq, BitVec.toNat_add, BitVec.toNat_eq, BitVec.toNat_allOnes]
  have hx := x.isLt
  change (x.toNat + 1) % 2^56 = 0 ↔ x.toNat = 2^56 - 1
  norm_num at hx ⊢
  omega

end P384
