import P384.BNBytes
import Mathlib.Data.Nat.Size

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option exponentiation.threshold 2048

namespace P384

theorem size_div_pow (x k : ℕ) : (x / 2^k).size = x.size - k := by
  have hle (n : ℕ) : (x / 2^k).size ≤ n ↔ x.size ≤ n + k := by
    rw [Nat.size_le, Nat.div_lt_iff_lt_mul (Nat.two_pow_pos k), Nat.size_le, pow_add]
  apply Nat.le_antisymm
  · apply (hle _).2
    omega
  · have h := (hle (x / 2^k).size).1 (Nat.le_refl _)
    omega

def bitOffsets : ℕ → ℕ → ℕ
  | 0, _ => 0
  | k + 1, x =>
      let shift := 2^k
      if x / 2^shift = 0 then bitOffsets k x else shift + bitOffsets k (x / 2^shift)

theorem bitOffsets_correct (k x : ℕ) (hx : x < 2^(2^k)) :
    (if x = 0 then 0 else 1) + bitOffsets k x = x.size := by
  induction k generalizing x with
  | zero =>
      have hb : x = 0 ∨ x = 1 := by norm_num at hx; omega
      rcases hb with rfl | rfl <;> simp [bitOffsets]
  | succ k ih =>
      have hp : (2 : ℕ)^(2^(k + 1)) = 2^(2^k) * 2^(2^k) := by
        rw [pow_succ (2 : ℕ) k, Nat.mul_two, pow_add]
      by_cases hz : x / 2^(2^k) = 0
      · have hsmall : x < 2^(2^k) := (Nat.div_eq_zero_iff_lt (Nat.two_pow_pos _)).1 hz
        simpa only [bitOffsets, if_pos hz] using ih x hsmall
      · have hsmall : x / 2^(2^k) < 2^(2^k) := by
          apply (Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _)).2
          simpa only [hp] using hx
        have hi := ih (x / 2^(2^k)) hsmall
        have hx0 : x ≠ 0 := by intro he; subst x; simp at hz
        have hl : 2^k < x.size := by
          rw [Nat.lt_size]
          have hn : ¬x < 2^(2^k) := by intro h; exact hz (Nat.div_eq_of_lt h)
          omega
        rw [if_neg hx0, bitOffsets, if_neg hz]
        rw [if_neg hz, size_div_pow] at hi
        omega

theorem bitOffsets_bound (k x : ℕ) : bitOffsets k x ≤ 2^k - 1 := by
  induction k generalizing x with
  | zero => simp [bitOffsets]
  | succ k ih =>
      have h0 := ih x
      have h1 := ih (x / 2^(2^k))
      have hp := Nat.two_pow_pos k
      simp only [bitOffsets, pow_succ]
      split <;> omega

end P384
