import P384.Field

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option exponentiation.threshold 2048

namespace P384

def unsigned {bits : ℕ} (x : BitVec bits) : ℤ := x.toNat

theorem unsigned_ofInt (bits : ℕ) (x : ℤ) :
    unsigned (BitVec.ofInt bits x) = x % 2^bits := by
  unfold unsigned
  rw [BitVec.toNat_ofInt, Int.toNat_of_nonneg (Int.emod_nonneg _ (by positivity))]
  norm_cast

theorem unsigned_ofInt_exact (bits : ℕ) (x : ℤ) (h : Within bits x) :
    unsigned (BitVec.ofInt bits x) = x := by
  rw [unsigned_ofInt, Int.emod_eq_of_lt h.1 h.2]

theorem ofInt_sub (bits : ℕ) (x y : ℤ) :
    BitVec.ofInt bits x - BitVec.ofInt bits y = BitVec.ofInt bits (x - y) := by
  apply BitVec.eq_of_toInt_eq
  simp

def machineNeg (a : Felem) : Felem := fun i =>
  unsigned (BitVec.ofInt 64 (pad64 i) - BitVec.ofInt 64 (a i))

theorem pad64_fits : ∀ i, Within 64 (pad64 i) := by unfold Within; decide

theorem machineNeg_refines (a : Felem) (ha : ∀ i, 0 ≤ a i ∧ a i ≤ pad64 i) :
    machineNeg a = neg a := by
  funext i
  dsimp only [machineNeg, neg]
  rw [ofInt_sub]
  apply unsigned_ofInt_exact
  have hi := ha i
  have hp := pad64_fits i
  unfold Within at *
  omega

theorem reduced_limbs_small (a : Felem) (ha : Reduced a) : ∀ i, Within 56 (a i) := by
  intro i
  by_cases hi : i.val < 6
  · let j : Fin 6 := ⟨i.val, hi⟩
    have hj := ha.1 j
    have he : j.castSucc = i := Fin.ext rfl
    rwa [he] at hj
  · have he : i = 6 := by apply Fin.ext; have := i.isLt; omega
    subst i
    obtain ⟨_, hlo, hhi⟩ := ha
    norm_num [Within] at *
    omega

theorem reduced_neg_no_underflow (a : Felem) (ha : Reduced a) :
    ∀ i, 0 ≤ a i ∧ a i ≤ pad64 i := by
  intro i
  have hi := reduced_limbs_small a ha i
  have hpad : (2^56 : ℤ) ≤ pad64 i := by fin_cases i <;> decide
  norm_num [Within] at hi hpad
  omega

theorem machineNeg_correct_reduced (a : Felem) (ha : Reduced a) :
    Congruent (eval7 (machineNeg a)) (-eval7 a) := by
  rw [machineNeg_refines a (reduced_neg_no_underflow a ha)]
  exact neg_correct a

end P384
