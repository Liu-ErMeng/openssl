import P384.ScalarBits

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option exponentiation.threshold 2048

namespace P384

def combIndex (n i : ℕ) : ℕ :=
  8 * scalarBit n (i + 285 : ℕ) +
    if i < 95 then 4 * scalarBit n (i + 190 : ℕ) +
      2 * scalarBit n (i + 95 : ℕ) + scalarBit n i else 0

def combCoefficient (idx : ℕ) : ℕ :=
  idx % 2 + 2^95 * (idx / 2 % 2) + 2^190 * (idx / 4 % 2) + 2^285 * (idx / 8 % 2)

theorem combIndex_bound (n i : ℕ) : combIndex n i < 16 := by
  have h0 := scalarBit_bound n i
  have h1 := scalarBit_bound n (i + 95 : ℕ)
  have h2 := scalarBit_bound n (i + 190 : ℕ)
  have h3 := scalarBit_bound n (i + 285 : ℕ)
  unfold combIndex
  split <;> omega

theorem combCoefficient_bits (a b c d : ℕ) (ha : a < 2) (hb : b < 2)
    (hc : c < 2) (hd : d < 2) :
    combCoefficient (8 * d + (4 * c + 2 * b + a)) =
      a + 2^95 * b + 2^190 * c + 2^285 * d := by
  unfold combCoefficient
  have h0 : (8 * d + (4 * c + 2 * b + a)) % 2 = a := by omega
  have h1 : (8 * d + (4 * c + 2 * b + a)) / 2 % 2 = b := by omega
  have h2 : (8 * d + (4 * c + 2 * b + a)) / 4 % 2 = c := by omega
  have h3 : (8 * d + (4 * c + 2 * b + a)) / 8 % 2 = d := by omega
  rw [h0, h1, h2, h3]

theorem combCoefficient_index (n i : ℕ) : combCoefficient (combIndex n i) =
    (if i < 95 then scalarBit n i + 2^95 * scalarBit n (i + 95 : ℕ) +
      2^190 * scalarBit n (i + 190 : ℕ) else 0) +
      2^285 * scalarBit n (i + 285 : ℕ) := by
  by_cases hi : i < 95
  · simp only [combIndex, if_pos hi]
    exact combCoefficient_bits _ _ _ _ (scalarBit_bound _ _) (scalarBit_bound _ _)
      (scalarBit_bound _ _) (scalarBit_bound _ _)
  · simp only [combIndex, if_neg hi, add_zero, zero_add]
    simpa using combCoefficient_bits 0 0 0 (scalarBit n (i + 285 : ℕ))
      (by decide) (by decide) (by decide) (scalarBit_bound _ _)

theorem sum_range_truncate {G : Type} [AddCommMonoid G]
    (k l : ℕ) (h : k ≤ l) (f : ℕ → G) :
    (∑ i ∈ Finset.range l, if i < k then f i else 0) = ∑ i ∈ Finset.range k, f i := by
  have he : l = k + (l - k) := by omega
  rw [he, Finset.sum_range_add]
  have ha : (∑ i ∈ Finset.range k, if i < k then f i else 0) = ∑ i ∈ Finset.range k, f i := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [if_pos (Finset.mem_range.mp hi)]
  rw [ha]
  simp

theorem binarySlice_sum (n start len : ℕ) :
    (∑ i ∈ Finset.range len, 2^i * scalarBit n (i + start : ℕ)) =
      n / 2^start % 2^len := by
  have h := binaryPrefix_shift len start n
  rw [binaryPrefix_value] at h
  simpa [Nat.add_comm] using h.symm

def combPrefix (n k : ℕ) : ℕ := ∑ i ∈ Finset.range k, 2^i * combCoefficient (combIndex n i)

theorem combPrefix_384 (n : ℕ) (hn : n < 2^384) : combPrefix n 99 = n := by
  have hf (k a : ℕ) :
      (∑ i ∈ Finset.range k, 2^i * (2^a * scalarBit n (i + a : ℕ))) =
      2^a * (∑ i ∈ Finset.range k, 2^i * scalarBit n (i + a : ℕ)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hs : combPrefix n 99 =
      (∑ i ∈ Finset.range 95, 2^i * scalarBit n i) +
      2^95 * (∑ i ∈ Finset.range 95, 2^i * scalarBit n (i + 95 : ℕ)) +
      2^190 * (∑ i ∈ Finset.range 95, 2^i * scalarBit n (i + 190 : ℕ)) +
      2^285 * (∑ i ∈ Finset.range 99, 2^i * scalarBit n (i + 285 : ℕ)) := by
    unfold combPrefix
    simp_rw [combCoefficient_index, mul_add, mul_ite, mul_zero]
    rw [Finset.sum_add_distrib, sum_range_truncate 95 99 (by decide)]
    simp_rw [mul_add, Finset.sum_add_distrib]
    rw [hf, hf, hf]
  rw [hs]
  have h0 := binarySlice_sum n 0 95
  have h1 := binarySlice_sum n 95 95
  have h2 := binarySlice_sum n 190 95
  have h3 := binarySlice_sum n 285 99
  simp only [Nat.add_zero, pow_zero, Nat.div_one] at h0
  rw [h0, h1, h2, h3]
  have hd : n / 2^285 < 2^99 := (Nat.div_lt_iff_lt_mul (by positivity)).2 (by
    simpa only [← pow_add] using hn)
  rw [Nat.mod_eq_of_lt hd]
  have h01 := Nat.mod_add_div n (2^95)
  have h12 := Nat.mod_add_div (n / 2^95) (2^95)
  have h23 := Nat.mod_add_div (n / 2^190) (2^95)
  have he1 : n / 2^95 / 2^95 = n / 2^190 := by rw [Nat.div_div_eq_div_mul, ← pow_add]
  have he2 : n / 2^190 / 2^95 = n / 2^285 := by rw [Nat.div_div_eq_div_mul, ← pow_add]
  rw [he1] at h12
  rw [he2] at h23
  linear_combination h01 + 2^95 * h12 + 2^190 * h23

end P384
