import P384.Reduction

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
set_option exponentiation.threshold 2048

namespace P384

def fieldValue (a : Felem) : ZMod p := (eval7 a : ℤ)

theorem field_mulReduce (a b : Felem) :
    fieldValue (mulReduce a b) = fieldValue a * fieldValue b := by
  have h := (ZMod.intCast_eq_intCast_iff' _ _ p).2 (mulReduce_correct a b)
  simpa only [fieldValue, Int.cast_mul] using h

theorem field_squareReduce (a : Felem) :
    fieldValue (squareReduce a) = fieldValue a * fieldValue a := by
  have h := (ZMod.intCast_eq_intCast_iff' _ _ p).2 (squareReduce_correct a)
  simpa only [fieldValue, Int.cast_pow, pow_two, Int.cast_mul] using h

theorem squares_pow {R : Type} [Monoid R] (x : R) (n : ℕ) :
    squares (fun y => y * y) n x = x ^ (2^n) := by
  induction n with
  | zero => simp [squares]
  | succ n ih => rw [squares, ih, ← pow_add]; congr 1; omega

theorem field_squares (a : Felem) (n : ℕ) :
    fieldValue (squares squareReduce n a) =
      squares (fun y => y * y) n (fieldValue a) := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [squares, field_squareReduce, ih]

def invLimbs (a : Felem) : Felem := invProgram squareReduce mulReduce a
def invChain {R : Type} [Monoid R] (x : R) : R :=
  invProgram (fun y => y * y) (fun y z => y * z) x

theorem squares_map {α β : Type} (f : α → β) (sa : α → α) (sb : β → β)
    (h : ∀ x, f (sa x) = sb (f x)) (n : ℕ) (x : α) :
    f (squares sa n x) = squares sb n (f x) := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [squares, h, ih]

theorem invProgram_map {α β : Type} (f : α → β)
    (sa : α → α) (ma : α → α → α) (sb : β → β) (mb : β → β → β)
    (hs : ∀ x, f (sa x) = sb (f x))
    (hm : ∀ x y, f (ma x y) = mb (f x) (f y)) (x : α) :
    f (invProgram sa ma x) = invProgram sb mb (f x) := by
  simp only [invProgram, hs, hm, squares_map f sa sb hs]

theorem invLimbs_field (a : Felem) : fieldValue (invLimbs a) = invChain (fieldValue a) := by
  simp only [invLimbs, invChain, invProgram, field_mulReduce, field_squareReduce,
    field_squares]

theorem invChain_exponent {R : Type} [Monoid R] (x : R) : invChain x = x ^ (p - 2) := by
  have h := invProgram_map (fun n : ℕ => x^n) (fun n => n + n) (fun n m => n + m)
    (fun y => y * y) (fun y z => y * z)
    (fun n => pow_add x n n) (fun n m => pow_add x n m) 1
  have he : invProgram (fun n : ℕ => n + n) (fun n m => n + m) 1 = p - 2 := by decide
  rw [he] at h
  simpa only [invChain, pow_one] using h.symm

theorem invLimbs_exponent (a : Felem) : fieldValue (invLimbs a) = fieldValue a ^ (p - 2) := by
  rw [invLimbs_field, invChain_exponent]

theorem invLimbs_correct (hp : p.Prime) (a : Felem) (ha : fieldValue a ≠ 0) :
    fieldValue a * fieldValue (invLimbs a) = 1 := by
  letI : Fact p.Prime := ⟨hp⟩
  rw [invLimbs_exponent, ← pow_succ']
  have h : p - 2 + 1 = p - 1 := by have := p_gt_two; omega
  rw [h]
  exact ZMod.pow_card_sub_one_eq_one ha

theorem invLimbs_zero (a : Felem) (ha : fieldValue a = 0) :
    fieldValue (invLimbs a) = 0 := by
  rw [invLimbs_exponent, ha]
  exact zero_pow (by have := p_gt_two; omega)

theorem invLimbs_reduced (a : Felem) (ha : Reduced a) : Reduced (invLimbs a) := by
  exact invProgram_preserves Reduced squareReduce mulReduce
    (fun x hx => squareReduce_bounds x (reduced_within61 x hx))
    (fun x y hx hy => mulReduce_bounds x y (reduced_within61 x hx) (reduced_within61 y hy)) a ha

end P384
