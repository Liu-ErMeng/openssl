import P384.Carry

set_option autoImplicit false
set_option maxHeartbeats 12000000
set_option exponentiation.threshold 2048

namespace P384

def contractPredicates (a : Felem) : Fin 5 → Prop :=
  ![a 6 = 2^48 - 1 ∧ a 5 = 2^56 - 1 ∧ a 4 = 2^56 - 1 ∧ a 3 = 2^56 - 1 ∧
      a 2 / 2^17 = 2^39 - 1,
    a 2 / 2^16 % 2 = 1,
    a 2 % 2^16 = 2^16 - 1 ∧ a 1 / 2^40 = 2^16 - 1,
    a 1 % 2^40 = 0 ∧ a 0 / 2^32 = 0,
    a 0 % 2^32 = 2^32 - 1]

def contractNeedsSubtract (a : Felem) : Prop :=
  contractPredicates a 0 ∧
    (contractPredicates a 1 ∨ (contractPredicates a 2 ∧
      (¬contractPredicates a 3 ∨ contractPredicates a 4)))

theorem contractNeedsSubtract_correct (a : Felem) (ha : serialFelem a) :
    contractNeedsSubtract a ↔ (p : ℤ) ≤ eval7 a := by
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
  have hd : a 2 / 2^16 / 2 = a 2 / 2^17 := by norm_num; omega
  change ((a 6 = 2^48 - 1 ∧ a 5 = 2^56 - 1 ∧ a 4 = 2^56 - 1 ∧ a 3 = 2^56 - 1 ∧
    a 2 / 2^17 = 2^39 - 1) ∧
      (a 2 / 2^16 % 2 = 1 ∨ ((a 2 % 2^16 = 2^16 - 1 ∧ a 1 / 2^40 = 2^16 - 1) ∧
        (¬(a 1 % 2^40 = 0 ∧ a 0 / 2^32 = 0) ∨ a 0 % 2^32 = 2^32 - 1)))) ↔ _
  norm_num [Within, eval7, radix, p] at h0 h1 h2 h3 h4 h5 h6 hd ⊢
  omega

end P384
