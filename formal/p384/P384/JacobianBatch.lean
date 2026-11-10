import P384.CurveGroup
import P384.ScalarPrecompute

set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace P384

def jacobianBatchDouble {K : Type} [Field K] (s : BatchState (Jacobian K)) : BatchState (Jacobian K) :=
  if s.skip then s else ⟨pointDouble s.acc, false⟩

def jacobianBatchAdd {K : Type} [Field K] [DecidableEq K]
    (s : BatchState (Jacobian K)) (q : Jacobian K) : BatchState (Jacobian K) :=
  ⟨if s.skip then q else pointAdd s.acc q, false⟩

def jacobianBatchAdds {K : Type} [Field K] [DecidableEq K] :
    List (Jacobian K) → BatchState (Jacobian K) → BatchState (Jacobian K)
  | [], s => s
  | q :: qs, s => jacobianBatchAdds qs (jacobianBatchAdd s q)

def jacobianBatchRound {K : Type} [Field K] [DecidableEq K] (events : List (Jacobian K))
    (s : BatchState (Jacobian K)) : BatchState (Jacobian K) :=
  jacobianBatchAdds events (jacobianBatchDouble s)

def jacobianBatchLoop {K : Type} [Field K] [DecidableEq K] (events : ℕ → List (Jacobian K)) :
    ℕ → BatchState (Jacobian K) → BatchState (Jacobian K)
  | 0, s => s
  | k + 1, s => jacobianBatchLoop events k (jacobianBatchRound (events k) s)

def BatchRep {K : Type} [Field K] (b : K) (s : BatchState (Jacobian K))
    (t : BatchState (shortCurve b).Point) : Prop := s.skip = t.skip ∧ Represents b s.acc t.acc

theorem jacobianBatchDouble_refines {K : Type} [Field K] (b : K)
    (s : BatchState (Jacobian K)) (t : BatchState (shortCurve b).Point)
    (hr : BatchRep b s t) (h2 : (2 : K) ≠ 0) :
    BatchRep b (jacobianBatchDouble s) (batchDouble t) := by
  obtain ⟨he, hp⟩ := hr
  cases hs : s.skip
  · have ht : t.skip = false := he.symm.trans hs
    simp only [jacobianBatchDouble, batchDouble, hs, ht, Bool.false_eq_true, if_false, BatchRep]
    exact ⟨by trivial, represents_double b s.acc t.acc hp h2⟩
  · have ht : t.skip = true := he.symm.trans hs
    simp only [jacobianBatchDouble, batchDouble, hs, ht, if_true]
    exact ⟨he, hp⟩

theorem jacobianBatchAdd_refines {K : Type} [Field K] [DecidableEq K] (b : K)
    (s : BatchState (Jacobian K)) (t : BatchState (shortCurve b).Point)
    (q : Jacobian K) (Q : (shortCurve b).Point) (hr : BatchRep b s t)
    (hq : Represents b q Q) (h2 : (2 : K) ≠ 0) :
    BatchRep b (jacobianBatchAdd s q) (batchAdd t Q) := by
  obtain ⟨he, hp⟩ := hr
  cases hs : s.skip
  · have ht : t.skip = false := he.symm.trans hs
    simp only [jacobianBatchAdd, batchAdd, hs, ht, Bool.false_eq_true, if_false, BatchRep]
    exact ⟨by trivial, represents_add b s.acc q t.acc Q hp hq h2⟩
  · have ht : t.skip = true := he.symm.trans hs
    simp only [jacobianBatchAdd, batchAdd, hs, ht, if_true, BatchRep]
    exact ⟨by trivial, hq⟩

theorem jacobianBatchAdds_refines {K : Type} [Field K] [DecidableEq K] (b : K)
    (events : List (Jacobian K)) (points : List (shortCurve b).Point)
    (s : BatchState (Jacobian K)) (t : BatchState (shortCurve b).Point)
    (he : List.Forall₂ (Represents b) events points) (hr : BatchRep b s t) (h2 : (2 : K) ≠ 0) :
    BatchRep b (jacobianBatchAdds events s) (batchAdds points t) := by
  induction he generalizing s t with
  | nil => exact hr
  | cons hp _ ih =>
      exact ih _ _ (jacobianBatchAdd_refines b s t _ _ hr hp h2)

theorem jacobianBatchRound_refines {K : Type} [Field K] [DecidableEq K] (b : K)
    (events : List (Jacobian K)) (points : List (shortCurve b).Point)
    (s : BatchState (Jacobian K)) (t : BatchState (shortCurve b).Point)
    (he : List.Forall₂ (Represents b) events points) (hr : BatchRep b s t) (h2 : (2 : K) ≠ 0) :
    BatchRep b (jacobianBatchRound events s) (batchRound points t) :=
  jacobianBatchAdds_refines b events points _ _ he (jacobianBatchDouble_refines b s t hr h2) h2

theorem jacobianBatchLoop_refines {K : Type} [Field K] [DecidableEq K] (b : K)
    (events : ℕ → List (Jacobian K)) (points : ℕ → List (shortCurve b).Point)
    (k : ℕ) (s : BatchState (Jacobian K)) (t : BatchState (shortCurve b).Point)
    (he : ∀ i < k, List.Forall₂ (Represents b) (events i) (points i))
    (hr : BatchRep b s t) (h2 : (2 : K) ≠ 0) :
    BatchRep b (jacobianBatchLoop events k s) (batchLoop points k t) := by
  induction k generalizing s t with
  | zero => exact hr
  | succ k ih =>
      exact ih _ _ (fun i hi => he i (by omega))
        (jacobianBatchRound_refines b _ _ s t (he k (by omega)) hr h2)

theorem jacobianBatchLoop_scalar_correct {K : Type} [Field K] [DecidableEq K] (b : K)
    (ps : List (ℕ × (shortCurve b).Point)) (g : Option (ℕ × (shortCurve b).Point))
    (events : ℕ → List (Jacobian K))
    (hp : ∀ q ∈ ps, q.1 < 2^384) (hg : ∀ q, g = some q → q.1 < 2^384)
    (he : ∀ i < (if ps.isEmpty then 99 else 381),
      List.Forall₂ (Represents b) (events i) (scalarEvents ps g i)) (h2 : (2 : K) ≠ 0) :
    Represents b (jacobianBatchLoop events (if ps.isEmpty then 99 else 381)
      ⟨⟨0, 0, 0⟩, true⟩).acc (generatorValue g + (ps.map (fun q => (q.1 : ℤ) • q.2)).sum) := by
  have hr : BatchRep b ⟨⟨0, 0, 0⟩, true⟩ ⟨0, true⟩ := ⟨rfl, rfl⟩
  have h := (jacobianBatchLoop_refines b events (scalarEvents ps g) _ _ _ he hr h2).2
  change Represents b _ (scalarMulLoop ps g) at h
  rwa [scalarMulLoop_correct ps g hp hg] at h

end P384
