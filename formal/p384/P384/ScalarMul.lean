import P384.BatchSchedule
import P384.ScalarWindows
import P384.Selection

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option exponentiation.threshold 2048

namespace P384

theorem comb_weighted_scalar (n : ℕ) (hn : n < 2^384) :
    (∑ i ∈ Finset.range 99, (2 : ℤ)^i * (combCoefficient (combIndex n i) : ℤ)) = n := by
  have h := congrArg (fun x : ℕ => (x : ℤ)) (combPrefix_384 n hn)
  simpa only [combPrefix, Nat.cast_sum, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat] using h

def generatorEvents {G : Type} [AddCommGroup G] (g : Option (ℕ × G)) (i : ℕ) : List G :=
  match g with
  | none => []
  | some q => if i < 99 then [(combCoefficient (combIndex q.1 i) : ℤ) • q.2] else []

def generatorValue {G : Type} [AddCommGroup G] : Option (ℕ × G) → G
  | none => 0
  | some q => (q.1 : ℤ) • q.2

theorem generatorEvents_weighted {G : Type} [AddCommGroup G] (g : Option (ℕ × G))
    (hn : ∀ q, g = some q → q.1 < 2^384) (k : ℕ) (hk : 99 ≤ k) :
    (∑ i ∈ Finset.range k, (2 : ℤ)^i • (generatorEvents g i).sum) = generatorValue g := by
  cases g with
  | none => simp [generatorEvents, generatorValue]
  | some q =>
      have hq := hn q rfl
      have hrow (i : ℕ) : (2 : ℤ)^i • (generatorEvents (some q) i).sum =
          if i < 99 then ((2 : ℤ)^i * (combCoefficient (combIndex q.1 i) : ℤ)) • q.2 else 0 := by
        by_cases hi : i < 99 <;> simp [generatorEvents, hi, mul_smul]
      simp_rw [hrow]
      rw [sum_range_truncate 99 k hk, ← Finset.sum_smul, comb_weighted_scalar q.1 hq]
      rfl

def scalarEvents {G : Type} [AddCommGroup G] (ps : List (ℕ × G)) (g : Option (ℕ × G))
    (i : ℕ) : List G := generatorEvents g i ++ ordinaryEvents ps i

def scalarMulLoop {G : Type} [AddCommGroup G] (ps : List (ℕ × G)) (g : Option (ℕ × G)) : G :=
  (batchLoop (scalarEvents ps g) (if ps.isEmpty then 99 else 381) ⟨0, true⟩).acc

theorem scalarMulLoop_correct {G : Type} [AddCommGroup G] (ps : List (ℕ × G))
    (g : Option (ℕ × G)) (hp : ∀ q ∈ ps, q.1 < 2^384)
    (hg : ∀ q, g = some q → q.1 < 2^384) :
    scalarMulLoop ps g = generatorValue g + (ps.map (fun q => (q.1 : ℤ) • q.2)).sum := by
  unfold scalarMulLoop
  rw [batchLoop_from_zero]
  cases ps with
  | nil =>
      simp only [List.isEmpty_nil, if_true, List.map_nil, List.sum_nil, add_zero]
      have he (i : ℕ) : (scalarEvents [] g i).sum = (generatorEvents g i).sum := by
        simp [scalarEvents, ordinaryEvents]
      simp_rw [he]
      exact generatorEvents_weighted g hg 99 (by decide)
  | cons q ps =>
      simp only [List.isEmpty_cons, Bool.false_eq_true, if_false]
      simp only [scalarEvents, List.sum_append, smul_add, Finset.sum_add_distrib]
      rw [generatorEvents_weighted g hg 381 (by decide), ordinaryEvents_weighted (q :: ps) hp]

def scalarByteMul {G : Type} [AddCommGroup G] (ps : List (List Byte × G))
    (g : Option (List Byte × G)) : G :=
  scalarMulLoop (ps.map (fun q => (leValue q.1, q.2)))
    (g.map (fun q => (leValue q.1, q.2)))

theorem scalarByteMul_correct {G : Type} [AddCommGroup G] (ps : List (List Byte × G))
    (g : Option (List Byte × G)) (hp : ∀ q ∈ ps, q.1.length = 48)
    (hg : ∀ q, g = some q → q.1.length = 48) :
    scalarByteMul ps g = generatorValue (g.map (fun q => (leValue q.1, q.2))) +
      (ps.map (fun q => (leValue q.1 : ℤ) • q.2)).sum := by
  have bound (bs : List Byte) (h : bs.length = 48) : leValue bs < 2^384 := by
    simpa [h] using leValue_bound bs
  unfold scalarByteMul
  rw [scalarMulLoop_correct]
  · simp [List.map_map, Function.comp_def]
  · intro q hq
    rcases List.mem_map.mp hq with ⟨r, hr, rfl⟩
    exact bound r.1 (hp r hr)
  · cases g with
    | none => simp
    | some r =>
        intro q hq
        have he : (leValue r.1, r.2) = q := by simpa using hq
        rw [← he]
        exact bound r.1 (hg r rfl)

end P384
