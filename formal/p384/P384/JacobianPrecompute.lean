import P384.JacobianBatch

set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace P384

def jacobianZero {K : Type} [Zero K] : Jacobian K := ⟨0, 0, 0⟩

def jacobianPrecomputeNext {K : Type} [Field K] [DecidableEq K] (p : Jacobian K)
    (table : List (Jacobian K)) (j : ℕ) : Jacobian K :=
  if j % 2 = 0 then pointDouble (table.getD (j / 2) jacobianZero)
  else pointAdd p (table.getD (j - 1) jacobianZero)

def jacobianPrecomputeTable {K : Type} [Field K] [DecidableEq K] (p : Jacobian K) :
    ℕ → List (Jacobian K)
  | 0 => [jacobianZero, p]
  | k + 1 => jacobianPrecomputeTable p k ++
      [jacobianPrecomputeNext p (jacobianPrecomputeTable p k) (k + 2)]

theorem jacobianPrecomputeTable_length {K : Type} [Field K] [DecidableEq K]
    (p : Jacobian K) (k : ℕ) : (jacobianPrecomputeTable p k).length = k + 2 := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [jacobianPrecomputeTable, List.length_append, List.length_singleton, ih]

theorem jacobianPrecomputeNext_rep {K : Type} [Field K] [DecidableEq K]
    (b : K) (p : Jacobian K) (P : (shortCurve b).Point) (table : List (Jacobian K))
    (j : ℕ) (hj : 2 ≤ j) (hp : Represents b p P)
    (ht : ∀ i < j, Represents b (table.getD i jacobianZero) (i • P)) (h2 : (2 : K) ≠ 0) :
    Represents b (jacobianPrecomputeNext p table j) (j • P) := by
  unfold jacobianPrecomputeNext
  split
  · rename_i he
    have h := represents_double b _ _ (ht (j / 2) (by omega)) h2
    have hn : j / 2 + j / 2 = j := by omega
    rwa [← add_nsmul, hn] at h
  · have h := represents_add b p _ P _ hp (ht (j - 1) (by omega)) h2
    have he : P + (j - 1) • P = j • P := by
      calc
        P + (j - 1) • P = (1 + (j - 1)) • P := by simp only [add_nsmul, one_nsmul]
        _ = j • P := by congr 1; omega
    rwa [he] at h

theorem jacobianPrecomputeTable_rep {K : Type} [Field K] [DecidableEq K]
    (b : K) (p : Jacobian K) (P : (shortCurve b).Point) (k : ℕ)
    (hp : Represents b p P) (h2 : (2 : K) ≠ 0) :
    ∀ j < k + 2, Represents b ((jacobianPrecomputeTable p k).getD j jacobianZero) (j • P) := by
  induction k with
  | zero =>
      intro j hj
      have h : j = 0 ∨ j = 1 := by omega
      rcases h with rfl | rfl
      · simp only [jacobianPrecomputeTable, List.getD_cons_zero, zero_nsmul]
        rfl
      · simpa only [jacobianPrecomputeTable, List.getD_cons_succ, List.getD_cons_zero, one_nsmul] using hp
  | succ k ih =>
      intro j hj
      rw [jacobianPrecomputeTable]
      by_cases hl : j < k + 2
      · rw [List.getD_append _ _ _ _ (by rw [jacobianPrecomputeTable_length]; exact hl)]
        exact ih j hl
      · have he : j = k + 2 := by omega
        subst j
        rw [List.getD_append_right _ _ _ _ (by rw [jacobianPrecomputeTable_length]),
          jacobianPrecomputeTable_length, Nat.sub_self, List.getD_cons_zero]
        exact jacobianPrecomputeNext_rep b p P _ _ (by omega) hp ih h2

end P384
