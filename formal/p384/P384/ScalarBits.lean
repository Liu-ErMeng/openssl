import P384.Bytes

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option exponentiation.threshold 2048

namespace P384

def scalarBit (n : ℕ) (i : ℤ) : ℕ := if i < 0 then 0 else n / 2^i.toNat % 2

theorem scalarBit_bound (n : ℕ) (i : ℤ) : scalarBit n i < 2 := by
  unfold scalarBit
  split <;> omega

theorem scalarBit_nat (n i : ℕ) : scalarBit n i = n / 2^i % 2 := by
  simp [scalarBit]

theorem scalarBit_negative (n : ℕ) : scalarBit n (-1) = 0 := by simp [scalarBit]

theorem scalarBit_high (n : ℕ) (hn : n < 2^384) (i : ℤ) (hi : 384 ≤ i) : scalarBit n i = 0 := by
  have hp : (2 : ℕ)^384 ≤ 2^i.toNat := Nat.pow_le_pow_of_le Nat.one_lt_two (by omega)
  have hlt : n < 2^i.toNat := hn.trans_le hp
  simp only [scalarBit, if_neg (show ¬i < 0 by omega), Nat.div_eq_of_lt hlt, Nat.zero_mod]

def machineGetBit (bs : List Byte) (i : ℤ) : Byte :=
  if i < 0 ∨ 384 ≤ i then 0 else
    (bs.getD (i.toNat / 8) 0 >>> (i.toNat % 8)) &&& 1

theorem byteBit_value (bs : List Byte) (j k : ℕ) (hk : k < 8) :
    ((bs.getD j 0 >>> k) &&& (1 : Byte)).toNat = leValue bs / 2^(8 * j + k) % 2 := by
  rw [← byteAt_leValue bs j]
  simp only [byteAt, BitVec.toNat_and, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat,
    Nat.shiftRight_eq_div_pow, show (1 : Byte).toNat = 1 from rfl, Nat.and_one_is_mod]
  have hp : (256 : ℕ)^j = 2^(8 * j) := by rw [pow_mul]; rfl
  have ht : ((leValue bs / 256^j % 256) / 2^k) % 2 = leValue bs / 256^j / 2^k % 2 := by
    have hd : (2 : ℕ)^k * 2^(8 - k) = 256 := by rw [← pow_add, Nat.add_sub_of_le (Nat.le_of_lt hk)]; rfl
    rw [← hd, Nat.mod_mul_right_div_self]
    have he : (2 : ℕ)^(8 - k) = 2 * 2^(7 - k) := by
      rw [← pow_succ', show 7 - k + 1 = 8 - k by omega]
    rw [he, Nat.mod_mul_right_mod]
  rw [ht, hp, Nat.div_div_eq_div_mul, ← pow_add]

theorem machineGetBit_correct (bs : List Byte) (hl : bs.length = 48) (i : ℤ) :
    (machineGetBit bs i).toNat = scalarBit (leValue bs) i := by
  have hn : leValue bs < 2^384 := by simpa [hl] using leValue_bound bs
  unfold machineGetBit
  by_cases hneg : i < 0
  · simp [hneg, scalarBit]
  · by_cases hhigh : 384 ≤ i
    · rw [if_pos (Or.inr hhigh), scalarBit_high _ hn i hhigh]
      rfl
    · rw [if_neg (by omega), byteBit_value bs (i.toNat / 8) (i.toNat % 8) (Nat.mod_lt _ (by decide))]
      rw [Nat.div_add_mod]
      simp only [scalarBit, if_neg hneg]

theorem machineGetBit_read_bound (i : ℤ) (hi : 0 ≤ i ∧ i < 384) :
    i.toNat / 8 < 48 ∧ i.toNat % 8 < 8 := by omega

def binaryPrefix : ℕ → ℕ → ℕ
  | 0, _ => 0
  | k + 1, n => binaryPrefix k n + 2^k * scalarBit n k

theorem binaryPrefix_value (k n : ℕ) : binaryPrefix k n = n % 2^k := by
  induction k with
  | zero => simp [binaryPrefix, Nat.mod_one]
  | succ k ih =>
      rw [binaryPrefix, ih, scalarBit_nat, pow_succ, Nat.mod_mul]

theorem binaryPrefix_shift (k i n : ℕ) :
    binaryPrefix k (n / 2^i) = ∑ j ∈ Finset.range k, 2^j * scalarBit n (i + j : ℕ) := by
  induction k with
  | zero => simp [binaryPrefix]
  | succ k ih =>
      rw [binaryPrefix, ih, Finset.sum_range_succ]
      congr 1
      simp only [scalarBit_nat, Nat.div_div_eq_div_mul, ← pow_add]

end P384
