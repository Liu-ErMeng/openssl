import P384.ContractCompare

set_option autoImplicit false
set_option maxHeartbeats 12000000
set_option exponentiation.threshold 2048

namespace P384

open Classical


noncomputable def contractSubtract (a : Felem) : Felem :=
  if contractNeedsSubtract a then
    if contractPredicates a 1 then
      ![a 0 - 2^32 + 1, a 1 + 2^40, a 2 % 2^16, 0, 0, 0, 0]
    else ![a 0 - 2^32 + 1, a 1 % 2^40, 0, 0, 0, 0, 0]
  else a

noncomputable def contractTail (a : Felem) : Felem := carry7 (contractSubtract a)
noncomputable def contractInteger (a : Felem) : Felem := contractTail (contractFirst a)

theorem serialFelem_value_bounds (a : Felem) (ha : serialFelem a) :
    0 ≤ eval7 a ∧ eval7 a < 2^384 := by
  have h0 := ha.1 0
  have h1 := ha.1 1
  have h2 := ha.1 2
  have h3 := ha.1 3
  have h4 := ha.1 4
  have h5 := ha.1 5
  have h6 := ha.2
  change Within 56 (a 0) at h0
  change Within 56 (a 1) at h1
  change Within 56 (a 2) at h2
  change Within 56 (a 3) at h3
  change Within 56 (a 4) at h4
  change Within 56 (a 5) at h5
  norm_num [Within, eval7, radix] at h0 h1 h2 h3 h4 h5 h6 ⊢
  omega

theorem contractSubtract_value (a : Felem) :
    eval7 (contractSubtract a) =
      if contractNeedsSubtract a then eval7 a - (p : ℤ) else eval7 a := by
  by_cases hs : contractNeedsSubtract a
  · have hp0 := hs.1
    change a 6 = 2^48 - 1 ∧ a 5 = 2^56 - 1 ∧ a 4 = 2^56 - 1 ∧ a 3 = 2^56 - 1 ∧
      a 2 / 2^17 = 2^39 - 1 at hp0
    obtain ⟨h6, h5, h4, h3, h2⟩ := hp0
    have hd : a 2 / 2^16 / 2 = a 2 / 2^17 := by norm_num; omega
    by_cases hb : contractPredicates a 1
    · have hbit : a 2 / 2^16 % 2 = 1 := hb
      have he : a 2 = (2^56 - 2^16) + a 2 % 2^16 := by
        norm_num at h2 hd hbit ⊢
        omega
      simp only [contractSubtract, if_pos hs, if_pos hb]
      simp only [eval7, Matrix.cons_val, h6, h5, h4, h3]
      norm_num [radix, p]
      omega
    · have hp2 := (hs.2.resolve_left hb).1
      change a 2 % 2^16 = 2^16 - 1 ∧ a 1 / 2^40 = 2^16 - 1 at hp2
      have hbit : ¬a 2 / 2^16 % 2 = 1 := hb
      have he2 : a 2 = 2^56 - 2^16 - 1 := by
        norm_num at h2 hd hbit hp2 ⊢
        omega
      have he1 : a 1 = (2^56 - 2^40) + a 1 % 2^40 := by
        norm_num at hp2 ⊢
        omega
      simp only [contractSubtract, if_pos hs, if_neg hb]
      simp only [eval7, Matrix.cons_val, h6, h5, h4, h3]
      norm_num [radix, p]
      omega
  · simp only [contractSubtract, if_neg hs]

theorem contractTail_correct (a : Felem) (ha : serialFelem a) :
    Congruent (eval7 (contractTail a)) (eval7 a) ∧
      (0 ≤ eval7 (contractTail a) ∧ eval7 (contractTail a) < (p : ℤ)) ∧
      serialFelem (contractTail a) := by
  have hv := serialFelem_value_bounds a ha
  have he : eval7 (contractTail a) =
      if contractNeedsSubtract a then eval7 a - (p : ℤ) else eval7 a := by
    rw [contractTail, carry7_value, contractSubtract_value a]
  have hb : 0 ≤ eval7 (contractTail a) ∧ eval7 (contractTail a) < (p : ℤ) := by
    rw [he]
    by_cases hs : contractNeedsSubtract a
    · rw [if_pos hs]
      have hh := (contractNeedsSubtract_correct a ha).1 hs
      norm_num [p] at hv hh ⊢
      omega
    · rw [if_neg hs]
      have hh : eval7 a < (p : ℤ) := by
        exact lt_of_not_ge (fun h => hs ((contractNeedsSubtract_correct a ha).2 h))
      exact ⟨hv.1, hh⟩
  refine ⟨?_, hb, ?_⟩
  · rw [he]
    by_cases hs : contractNeedsSubtract a
    · rw [if_pos hs]
      exact congruent_of_multiple _ _ (-1) (by ring)
    · rw [if_neg hs]
      rfl
  · apply serialFelem_of_value _ (carry7_low_bounds _)
    refine ⟨hb.1, hb.2.trans ?_⟩
    norm_num [p]

theorem contractInteger_correct (a : Felem) (ha : Reduced a) :
    eval7 (contractInteger a) = eval7 a % (p : ℤ) ∧ serialFelem (contractInteger a) := by
  have hf := contractFirst_correct a ha
  have ht := contractTail_correct (contractFirst a) hf.2
  have hc := congruent_trans ht.1 hf.1
  have hb := ht.2.1
  refine ⟨?_, ht.2.2⟩
  change eval7 (contractInteger a) % (p : ℤ) = eval7 a % (p : ℤ) at hc
  change 0 ≤ eval7 (contractInteger a) ∧ eval7 (contractInteger a) < (p : ℤ) at hb
  rwa [Int.emod_eq_of_lt hb.1 hb.2] at hc

theorem contractSubtract_zero_bounds (a : Felem) (ha : serialFelem a) :
    -2^32 ≤ contractSubtract a 0 ∧ contractSubtract a 0 < 2^56 := by
  have h0 := ha.1 0
  change Within 56 (a 0) at h0
  unfold contractSubtract
  split_ifs <;> change -2^32 ≤ _ ∧ _ < 2^56 <;>
    norm_num [Matrix.cons_val, Within] at h0 ⊢ <;> omega

theorem contractSubtract_bounds (a : Felem) (ha : serialFelem a) :
    ∀ i, -2^57 ≤ contractSubtract a i ∧ contractSubtract a i < 2^57 := by
  have h0 := serialFelem_limb_bound a ha 0
  have h1 := serialFelem_limb_bound a ha 1
  have hb0 : -2^57 ≤ a 0 - 2^32 + 1 ∧ a 0 - 2^32 + 1 < 2^57 := by
    norm_num [Within] at h0 ⊢
    omega
  have hb1 : -2^57 ≤ a 1 + 2^40 ∧ a 1 + 2^40 < 2^57 := by
    norm_num [Within] at h1 ⊢
    omega
  have hb2 : -2^57 ≤ a 2 % 2^16 ∧ a 2 % 2^16 < 2^57 := by omega
  have hb40 : -2^57 ≤ a 1 % 2^40 ∧ a 1 % 2^40 < 2^57 := by omega
  have hz : (-2^57 : ℤ) ≤ 0 ∧ (0 : ℤ) < 2^57 := by norm_num
  by_cases hs : contractNeedsSubtract a
  · by_cases ht : contractPredicates a 1
    · simp only [contractSubtract, if_pos hs, if_pos ht]
      intro i
      fin_cases i <;> first | exact hb0 | exact hb1 | exact hb2 | exact hz
    · simp only [contractSubtract, if_pos hs, if_neg ht]
      intro i
      fin_cases i <;> first | exact hb0 | exact hb40 | exact hz
  · simp only [contractSubtract, if_neg hs]
    intro i
    have hi := serialFelem_limb_bound a ha i
    norm_num [Within] at hi ⊢
    omega

end P384
