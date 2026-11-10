import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FinCases
import Mathlib.FieldTheory.Finite.Basic

set_option autoImplicit false

namespace P384

def p : ℕ := 2^384 - 2^128 - 2^96 + 2^32 - 1
def radix : ℤ := 2^56
abbrev Felem := Fin 7 → ℤ
abbrev Widefelem := Fin 13 → ℤ

def squares {α : Type} (sq : α → α) : ℕ → α → α
  | 0, x => x
  | n + 1, x => sq (squares sq n x)

theorem squares_preserves {α : Type} (sq : α → α) (prop : α → Prop)
    (hs : ∀ x, prop x → prop (sq x)) (n : ℕ) (x : α) (hx : prop x) :
    prop (squares sq n x) := by
  induction n with
  | zero => exact hx
  | succ n ih => exact hs _ ih

def eval7 (a : Felem) : ℤ :=
  a 0 + a 1 * radix + a 2 * radix^2 + a 3 * radix^3 +
    a 4 * radix^4 + a 5 * radix^5 + a 6 * radix^6

def eval13 (a : Widefelem) : ℤ :=
  a 0 + a 1 * radix + a 2 * radix^2 + a 3 * radix^3 +
    a 4 * radix^4 + a 5 * radix^5 + a 6 * radix^6 +
    a 7 * radix^7 + a 8 * radix^8 + a 9 * radix^9 +
    a 10 * radix^10 + a 11 * radix^11 + a 12 * radix^12

def Congruent (x y : ℤ) : Prop := x % (p : ℤ) = y % (p : ℤ)
def Within (bits : ℕ) (x : ℤ) : Prop := 0 ≤ x ∧ x < 2^bits

theorem bounds_add {x y lo hi lo' hi' : ℤ}
    (hx : lo ≤ x ∧ x ≤ hi) (hy : lo' ≤ y ∧ y ≤ hi') :
    lo + lo' ≤ x + y ∧ x + y ≤ hi + hi' := by omega

theorem bounds_sub {x y lo hi lo' hi' : ℤ}
    (hx : lo ≤ x ∧ x ≤ hi) (hy : lo' ≤ y ∧ y ≤ hi') :
    lo - hi' ≤ x - y ∧ x - y ≤ hi - lo' := by omega

theorem bounds_scale {x lo hi : ℤ} (hx : lo ≤ x ∧ x ≤ hi)
    (k : ℤ) (hk : 0 ≤ k) : lo * k ≤ x * k ∧ x * k ≤ hi * k := by
  constructor
  · exact mul_le_mul_of_nonneg_right hx.1 hk
  · exact mul_le_mul_of_nonneg_right hx.2 hk

theorem bounds_div {x lo hi : ℤ} (hx : lo ≤ x ∧ x ≤ hi)
    (k : ℤ) (hk : 0 < k) : lo / k ≤ x / k ∧ x / k ≤ hi / k :=
  ⟨Int.ediv_le_ediv hk hx.1, Int.ediv_le_ediv hk hx.2⟩

theorem bounds_mod (x k : ℤ) (hk : 0 < k) : 0 ≤ x % k ∧ x % k ≤ k - 1 :=
  ⟨Int.emod_nonneg _ (ne_of_gt hk), by have := Int.emod_lt_of_pos x hk; omega⟩

theorem within_of_bounds {x lo hi : ℤ} (h : lo ≤ x ∧ x ≤ hi)
    (bits : ℕ) (hlo : 0 ≤ lo) (hhi : hi < 2^bits) : Within bits x :=
  ⟨hlo.trans h.1, h.2.trans_lt hhi⟩

def Reduced (a : Felem) : Prop :=
  (∀ i : Fin 6, Within 56 (a i.castSucc)) ∧ 0 ≤ a 6 ∧ a 6 ≤ 2^48

theorem p_pos : 0 < p := by norm_num [p]
theorem p_gt_two : 2 < p := by norm_num [p]

theorem congruent_of_multiple (x y k : ℤ) (h : x = y + (p : ℤ) * k) :
    Congruent x y := by
  unfold Congruent
  rw [h]
  simp

theorem congruent_trans {x y z : ℤ} (h : Congruent x y) (h' : Congruent y z) :
    Congruent x z := h.trans h'

theorem reduced_value_bounds (a : Felem) (h : Reduced a) :
    0 ≤ eval7 a ∧ eval7 a < 2 * (p : ℤ) := by
  obtain ⟨h, h6, h6'⟩ := h
  have h0 := h 0
  have h1 := h 1
  have h2 := h 2
  have h3 := h 3
  have h4 := h 4
  have h5 := h 5
  change Within 56 (a 0) at h0
  change Within 56 (a 1) at h1
  change Within 56 (a 2) at h2
  change Within 56 (a 3) at h3
  change Within 56 (a 4) at h4
  change Within 56 (a 5) at h5
  norm_num [Within] at h0 h1 h2 h3 h4 h5
  norm_num [eval7, radix, p] at *
  constructor <;> omega

theorem reduced_within61 (a : Felem) (h : Reduced a) : ∀ i, Within 61 (a i) := by
  intro i
  by_cases hi : i.val < 6
  · let j : Fin 6 := ⟨i.val, hi⟩
    have hj := h.1 j
    have he : j.castSucc = i := Fin.ext rfl
    rw [he] at hj
    norm_num [Within] at hj ⊢
    omega
  · have he : i = 6 := by apply Fin.ext; have := i.isLt; omega
    subst i
    obtain ⟨_, hlo, hhi⟩ := h
    norm_num [Within] at *
    omega

end P384
