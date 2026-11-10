import P384.ScalarMul
import Mathlib.Data.List.GetD

set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace P384

def precomputeNext {G : Type} [AddZeroClass G] (p : G) (table : List G) (j : ℕ) : G :=
  if j % 2 = 0 then table.getD (j / 2) 0 + table.getD (j / 2) 0
  else p + table.getD (j - 1) 0

def precomputeTable {G : Type} [AddZeroClass G] (p : G) : ℕ → List G
  | 0 => [0, p]
  | k + 1 => precomputeTable p k ++ [precomputeNext p (precomputeTable p k) (k + 2)]

theorem precomputeTable_length {G : Type} [AddZeroClass G] (p : G) (k : ℕ) :
    (precomputeTable p k).length = k + 2 := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [precomputeTable, List.length_append, List.length_singleton, ih]

theorem precomputeNext_correct {G : Type} [AddMonoid G] (p : G) (table : List G)
    (j : ℕ) (hj : 2 ≤ j) (ht : ∀ i < j, table.getD i 0 = i • p) :
    precomputeNext p table j = j • p := by
  unfold precomputeNext
  split
  · rename_i he
    rw [ht (j / 2) (by omega), ← add_nsmul]
    congr 1
    omega
  · rw [ht (j - 1) (by omega)]
    calc
      p + (j - 1) • p = (1 + (j - 1)) • p := by simp only [add_nsmul, one_nsmul]
      _ = j • p := by congr 1; omega

theorem precomputeTable_correct {G : Type} [AddMonoid G] (p : G) (k : ℕ) :
    ∀ j < k + 2, (precomputeTable p k).getD j 0 = j • p := by
  induction k with
  | zero =>
      intro j hj
      have h : j = 0 ∨ j = 1 := by omega
      rcases h with rfl | rfl <;> simp [precomputeTable]
  | succ k ih =>
      intro j hj
      rw [precomputeTable]
      by_cases hl : j < k + 2
      · rw [List.getD_append _ _ _ _ (by rw [precomputeTable_length]; exact hl)]
        exact ih j hl
      · have he : j = k + 2 := by omega
        subst j
        rw [List.getD_append_right _ _ _ _ (by rw [precomputeTable_length]),
          precomputeTable_length, Nat.sub_self, List.getD_cons_zero]
        exact precomputeNext_correct p _ _ (by omega) ih

theorem precompute17_correct {G : Type} [AddMonoid G] (p : G) (j : ℕ) (hj : j < 17) :
    (precomputeTable p 15).getD j 0 = j • p := precomputeTable_correct p 15 j hj

theorem precompute17_read_bounds (j : ℕ) (hj : 2 ≤ j ∧ j ≤ 16) :
    j / 2 < j ∧ j - 1 < j ∧ j < 17 := by omega

end P384
