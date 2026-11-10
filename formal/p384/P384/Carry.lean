import P384.Serialization
import P384.SignedWords

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option exponentiation.threshold 2048

namespace P384

def carryTerms (a : Felem) : Felem :=
  let t0 := a 0
  let t1 := a 1 + t0 / radix
  let t2 := a 2 + t1 / radix
  let t3 := a 3 + t2 / radix
  let t4 := a 4 + t3 / radix
  let t5 := a 5 + t4 / radix
  let t6 := a 6 + t5 / radix
  ![t0, t1, t2, t3, t4, t5, t6]

def carry7 (a : Felem) : Felem :=
  let t0 := a 0
  let t1 := a 1 + t0 / radix
  let t2 := a 2 + t1 / radix
  let t3 := a 3 + t2 / radix
  let t4 := a 4 + t3 / radix
  let t5 := a 5 + t4 / radix
  let t6 := a 6 + t5 / radix
  ![t0 % radix, t1 % radix, t2 % radix, t3 % radix,
    t4 % radix, t5 % radix, t6]

theorem carry7_value (a : Felem) : eval7 (carry7 a) = eval7 a := by
  simp only [carry7, eval7, Matrix.cons_val, Int.emod_def]
  ring

theorem carry7_low_bounds (a : Felem) (i : Fin 6) : Within 56 (carry7 a i.castSucc) := by
  have hp : (0 : ℤ) < radix := by norm_num [radix]
  fin_cases i <;> simp only [carry7, Matrix.cons_val, Fin.castSucc_mk] <;>
    exact ⟨Int.emod_nonneg _ (ne_of_gt hp), Int.emod_lt_of_pos _ hp⟩

theorem serialFelem_of_value (a : Felem)
    (hl : ∀ i : Fin 6, Within 56 (a i.castSucc))
    (hv : 0 ≤ eval7 a ∧ eval7 a < 2^384) : serialFelem a := by
  refine ⟨hl, ?_⟩
  have h0 := hl 0
  have h1 := hl 1
  have h2 := hl 2
  have h3 := hl 3
  have h4 := hl 4
  have h5 := hl 5
  change Within 56 (a 0) at h0
  change Within 56 (a 1) at h1
  change Within 56 (a 2) at h2
  change Within 56 (a 3) at h3
  change Within 56 (a 4) at h4
  change Within 56 (a 5) at h5
  norm_num [Within, eval7, radix] at h0 h1 h2 h3 h4 h5 hv ⊢
  omega

theorem carry7_serial (a : Felem) (hv : 0 ≤ eval7 a ∧ eval7 a < 2^384) :
    serialFelem (carry7 a) := by
  apply serialFelem_of_value _ (carry7_low_bounds a)
  rwa [carry7_value]

def contractHighBit (a : Felem) : ℤ := a 6 / 2^48

def contractFold (a : Felem) : Felem :=
  let h := contractHighBit a
  ![a 0 + h - h * 2^32, a 1 + h * 2^40, a 2 + h * 2^16,
    a 3, a 4, a 5, a 6 % 2^48]

def contractFirst (a : Felem) : Felem := carry7 (contractFold a)

theorem contractHighBit_cases (a : Felem) (ha : Reduced a) :
    contractHighBit a = 0 ∨ (contractHighBit a = 1 ∧ a 6 = 2^48) := by
  have hn := ha.2
  norm_num [contractHighBit] at hn ⊢
  omega

theorem contractFold_value (a : Felem) :
    eval7 (contractFold a) = eval7 a - (p : ℤ) * contractHighBit a := by
  simp only [contractFold, eval7, Matrix.cons_val, Int.emod_def]
  norm_num [p, radix, contractHighBit]
  ring

theorem contractFold_bounds (a : Felem) (ha : Reduced a) :
    0 ≤ eval7 (contractFold a) ∧ eval7 (contractFold a) < 2^384 := by
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
  rw [contractFold_value]
  rcases contractHighBit_cases a ha with hz | ⟨ho, ht⟩
  · rw [hz]
    have hb : a 6 < 2^48 := by
      norm_num [contractHighBit] at hz
      norm_num at h6 ⊢
      omega
    norm_num [Within, eval7, radix] at h0 h1 h2 h3 h4 h5 h6 hb ⊢
    omega
  · rw [ho]
    unfold eval7
    rw [ht]
    norm_num [Within, eval7, radix, p] at h0 h1 h2 h3 h4 h5 ⊢
    omega

theorem contractFirst_correct (a : Felem) (ha : Reduced a) :
    Congruent (eval7 (contractFirst a)) (eval7 a) ∧ serialFelem (contractFirst a) := by
  constructor
  · rw [contractFirst, carry7_value]
    exact congruent_of_multiple _ _ (-contractHighBit a) (by rw [contractFold_value]; ring)
  · exact carry7_serial _ (contractFold_bounds a ha)

theorem contractFold_zero_bounds (a : Felem) (ha : Reduced a) :
    -2^32 ≤ contractFold a 0 ∧ contractFold a 0 < 2^56 := by
  have h0 := ha.1 0
  change Within 56 (a 0) at h0
  rcases contractHighBit_cases a ha with hz | ⟨ho, _⟩
  · norm_num [contractFold, Matrix.cons_val, hz, Within] at h0 ⊢
    omega
  · norm_num [contractFold, Matrix.cons_val, ho, Within] at h0 ⊢
    omega

theorem contractCarryTerms_bounds (a : Felem) (ha : Reduced a) :
    ∀ i : Fin 6, Within 57 (carryTerms (contractFold a) i.succ) := by
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
  let bit := contractHighBit a
  have hbit : 0 ≤ bit ∧ bit ≤ 1 := by
    rcases contractHighBit_cases a ha with hz | ⟨ho, _⟩ <;> simp [bit, *]
  let t0 := a 0 + bit - bit * 2^32
  let t1 := a 1 + bit * 2^40 + t0 / radix
  let t2 := a 2 + bit * 2^16 + t1 / radix
  let t3 := a 3 + t2 / radix
  let t4 := a 4 + t3 / radix
  let t5 := a 5 + t4 / radix
  let t6 := a 6 % 2^48 + t5 / radix
  intro i
  fin_cases i
  · change Within 57 t1
    dsimp only [t1, t0]
    norm_num [Within, radix] at *
    omega
  · change Within 57 t2
    dsimp only [t2, t1, t0]
    norm_num [Within, radix] at *
    omega
  · change Within 57 t3
    dsimp only [t3, t2, t1, t0]
    norm_num [Within, radix] at *
    omega
  · change Within 57 t4
    dsimp only [t4, t3, t2, t1, t0]
    norm_num [Within, radix] at *
    omega
  · change Within 57 t5
    dsimp only [t5, t4, t3, t2, t1, t0]
    norm_num [Within, radix] at *
    omega
  · change Within 57 t6
    dsimp only [t6, t5, t4, t3, t2, t1, t0]
    norm_num [Within, radix] at *
    omega

end P384
