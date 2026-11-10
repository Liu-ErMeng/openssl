import P384.Booth
import P384.Comb
import Mathlib.Tactic.Abel

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option exponentiation.threshold 2048

namespace P384

structure BatchState (G : Type) where
  acc : G
  skip : Bool

def BatchValid {G : Type} [Zero G] (s : BatchState G) : Prop := s.skip = true → s.acc = 0

def batchDouble {G : Type} [Add G] (s : BatchState G) : BatchState G :=
  if s.skip then s else ⟨s.acc + s.acc, false⟩

def batchAdd {G : Type} [Add G] (s : BatchState G) (q : G) : BatchState G :=
  ⟨if s.skip then q else s.acc + q, false⟩

def batchAdds {G : Type} [Add G] : List G → BatchState G → BatchState G
  | [], s => s
  | q :: qs, s => batchAdds qs (batchAdd s q)

def batchRound {G : Type} [Add G] (events : List G) (s : BatchState G) : BatchState G :=
  batchAdds events (batchDouble s)

def batchLoop {G : Type} [Add G] (events : ℕ → List G) : ℕ → BatchState G → BatchState G
  | 0, s => s
  | k + 1, s => batchLoop events k (batchRound (events k) s)

theorem batchDouble_valid {G : Type} [AddZeroClass G] (s : BatchState G) (h : BatchValid s) :
    BatchValid (batchDouble s) := by
  cases hs : s.skip
  · simp [batchDouble, hs, BatchValid]
  · simpa [batchDouble, hs] using h

theorem batchDouble_acc {G : Type} [AddZeroClass G] (s : BatchState G) (h : BatchValid s) :
    (batchDouble s).acc = s.acc + s.acc := by
  cases hs : s.skip
  · simp [batchDouble, hs]
  · simp [batchDouble, hs, h hs]

theorem batchAdd_valid {G : Type} [AddZeroClass G] (s : BatchState G) (q : G) :
    BatchValid (batchAdd s q) := by simp [BatchValid, batchAdd]

theorem batchAdd_acc {G : Type} [AddZeroClass G] (s : BatchState G) (h : BatchValid s) (q : G) :
    (batchAdd s q).acc = s.acc + q := by
  cases hs : s.skip
  · simp [batchAdd, hs]
  · simp [batchAdd, hs, h hs]

theorem batchAdds_valid {G : Type} [AddZeroClass G] (qs : List G) (s : BatchState G)
    (h : BatchValid s) : BatchValid (batchAdds qs s) := by
  induction qs generalizing s with
  | nil => exact h
  | cons q qs ih => exact ih _ (batchAdd_valid s q)

theorem batchAdds_acc {G : Type} [AddMonoid G] (qs : List G) (s : BatchState G)
    (h : BatchValid s) : (batchAdds qs s).acc = s.acc + qs.sum := by
  induction qs generalizing s with
  | nil => simp [batchAdds]
  | cons q qs ih =>
      rw [batchAdds, ih _ (batchAdd_valid s q), batchAdd_acc s h q, List.sum_cons, add_assoc]

theorem batchRound_valid {G : Type} [AddZeroClass G] (events : List G) (s : BatchState G)
    (h : BatchValid s) : BatchValid (batchRound events s) :=
  batchAdds_valid events _ (batchDouble_valid s h)

theorem batchRound_acc {G : Type} [AddMonoid G] (events : List G) (s : BatchState G)
    (h : BatchValid s) : (batchRound events s).acc = s.acc + s.acc + events.sum := by
  rw [batchRound, batchAdds_acc _ _ (batchDouble_valid s h), batchDouble_acc s h]

theorem batchLoop_acc {G : Type} [AddCommGroup G] (events : ℕ → List G)
    (k : ℕ) (s : BatchState G) (h : BatchValid s) :
    (batchLoop events k s).acc = (2 : ℤ)^k • s.acc +
      ∑ i ∈ Finset.range k, (2 : ℤ)^i • (events i).sum := by
  induction k generalizing s with
  | zero => simp [batchLoop]
  | succ k ih =>
      rw [batchLoop, ih _ (batchRound_valid _ s h), batchRound_acc _ s h,
        Finset.sum_range_succ, pow_succ]
      simp only [smul_add, mul_smul, show (2 : ℤ) = 1 + 1 from rfl, add_smul, one_smul]
      abel

theorem batchLoop_from_zero {G : Type} [AddCommGroup G] (events : ℕ → List G) (k : ℕ) :
    (batchLoop events k ⟨0, true⟩).acc =
      ∑ i ∈ Finset.range k, (2 : ℤ)^i • (events i).sum := by
  rw [batchLoop_acc events k _ (by simp [BatchValid]), smul_zero, zero_add]

theorem sum_every_five {G : Type} [AddCommMonoid G] (f : ℕ → G) :
    (∑ i ∈ Finset.range 381, if i % 5 = 0 then f (i / 5) else 0) =
      ∑ j ∈ Finset.range 77, f j := by
  rw [← Finset.sum_filter]
  apply Finset.sum_bij (fun i _ => i / 5)
  · intro i hi
    simp only [Finset.mem_filter, Finset.mem_range] at hi ⊢
    omega
  · intro i hi j hj he
    simp only [Finset.mem_filter, Finset.mem_range] at hi hj
    omega
  · intro j hj
    refine ⟨5 * j, ?_, ?_⟩
    · simp only [Finset.mem_filter, Finset.mem_range] at hj ⊢
      omega
    · omega
  · intro i _
    rfl

theorem boothPrefix_sum (n k : ℕ) :
    boothPrefix n k = ∑ j ∈ Finset.range k, (32 : ℤ)^j * boothValue (boothWindow n j) := by
  induction k with
  | zero => simp [boothPrefix]
  | succ k ih => rw [boothPrefix, ih, Finset.sum_range_succ]

theorem ordinary_weighted_scalar (n : ℕ) (hn : n < 2^384) :
    (∑ i ∈ Finset.range 381, (2 : ℤ)^i *
      (if i % 5 = 0 then boothValue (boothWindow n (i / 5)) else 0)) = n := by
  have he : (∑ i ∈ Finset.range 381, (2 : ℤ)^i *
      (if i % 5 = 0 then boothValue (boothWindow n (i / 5)) else 0)) =
      ∑ i ∈ Finset.range 381, if i % 5 = 0 then
        (32 : ℤ)^(i / 5) * boothValue (boothWindow n (i / 5)) else 0 := by
    apply Finset.sum_congr rfl
    intro i _
    by_cases hi : i % 5 = 0
    · rw [if_pos hi, if_pos hi]
      have hx : i = 5 * (i / 5) := by omega
      rw [hx, pow_mul]
      norm_num
    · simp [hi]
  rw [he, sum_every_five (fun j => (32 : ℤ)^j * boothValue (boothWindow n j)),
    ← boothPrefix_sum, boothPrefix_384 n hn]

def ordinaryEvents {G : Type} [AddCommGroup G] (ps : List (ℕ × G)) (i : ℕ) : List G :=
  if i % 5 = 0 then ps.map (fun q => boothValue (boothWindow q.1 (i / 5)) • q.2) else []

theorem ordinaryEvents_weighted {G : Type} [AddCommGroup G] (ps : List (ℕ × G))
    (hn : ∀ q ∈ ps, q.1 < 2^384) :
    (∑ i ∈ Finset.range 381, (2 : ℤ)^i • (ordinaryEvents ps i).sum) =
      (ps.map (fun q => (q.1 : ℤ) • q.2)).sum := by
  induction ps with
  | nil => simp [ordinaryEvents]
  | cons q ps ih =>
      have hq : q.1 < 2^384 := hn q (by simp)
      have ht : ∀ r ∈ ps, r.1 < 2^384 := fun r hr => hn r (by simp [hr])
      have hrow (i : ℕ) : (ordinaryEvents (q :: ps) i).sum =
          (if i % 5 = 0 then boothValue (boothWindow q.1 (i / 5)) else 0) • q.2 +
          (ordinaryEvents ps i).sum := by
        by_cases hi : i % 5 = 0 <;> simp [ordinaryEvents, hi]
      simp_rw [hrow, smul_add, smul_smul]
      rw [Finset.sum_add_distrib, ← Finset.sum_smul, ordinary_weighted_scalar q.1 hq, ih ht]
      rfl

end P384
