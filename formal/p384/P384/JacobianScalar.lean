import P384.JacobianPrecompute
import P384.ScalarTable
import P384.ScalarNegation
import Mathlib.Data.List.Forall2

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192
set_option exponentiation.threshold 2048

namespace P384

structure JacobianScalarInput where
  scalar : List Byte
  point : Jacobian (ZMod p)
  value : P384Point

def JacobianScalarValid (q : JacobianScalarInput) : Prop :=
  q.scalar.length = 48 ∧ Represents (nistB : ZMod p) q.point q.value

def jacobianOrdinaryEvent (q : JacobianScalarInput) (i : ℕ) : Jacobian (ZMod p) :=
  let result := machineBoothRecode ((machineBoothWindow q.scalar i).setWidth 8)
  let selected := (jacobianPrecomputeTable q.point 15).getD result.2.toNat jacobianZero
  if result.1 = 0 then selected else jacobianNeg selected

theorem jacobianOrdinaryEvent_rep (q : JacobianScalarInput) (hq : JacobianScalarValid q) (j : ℕ) :
    Represents (nistB : ZMod p) (jacobianOrdinaryEvent q (5 * j))
      (boothValue (boothWindow (leValue q.scalar) j) • q.value) := by
  let result := machineBoothRecode ((machineBoothWindow q.scalar (5 * j)).setWidth 8)
  have hd := machineBoothWindow_recode q.scalar hq.1 j
  change result.1.toNat ≤ 1 ∧ result.2.toNat ≤ 16 ∧
    signedDigit result.1 result.2 = boothValue (boothWindow (leValue q.scalar) j) at hd
  have ht := jacobianPrecomputeTable_rep (nistB : ZMod p) q.point q.value 15 hq.2
    (by decide) result.2.toNat (by omega)
  have ht' : Represents (nistB : ZMod p)
      ((jacobianPrecomputeTable q.point 15).getD result.2.toNat jacobianZero)
      ((result.2.toNat : ℤ) • q.value) := by simpa only [natCast_zsmul] using ht
  change Represents _ (if result.1 = 0 then _ else _) _
  by_cases hs : result.1 = 0
  · rw [if_pos hs]
    have hv := hd.2.2
    simp only [signedDigit, if_pos hs] at hv
    rwa [hv] at ht'
  · rw [if_neg hs]
    have h := represents_neg (nistB : ZMod p) _ _ ht'
    have hv := hd.2.2
    simp only [signedDigit, if_neg hs] at hv
    rw [← neg_zsmul, hv] at h
    exact h

def jacobianGeneratorEvent (bs : List Byte) (i : ℕ) : Jacobian (ZMod p) :=
  builtinJacobian ⟨(machineCombWindow bs i).toNat % 16, Nat.mod_lt _ (by decide)⟩

theorem jacobianGeneratorEvent_rep (bs : List Byte) (hl : bs.length = 48) (i : ℕ) :
    Represents (nistB : ZMod p) (jacobianGeneratorEvent bs i)
      ((combCoefficient (combIndex (leValue bs) i) : ℤ) • builtinCurvePoint 1) := by
  have hv := machineCombWindow_correct bs hl i
  have hb := combIndex_bound (leValue bs) i
  unfold jacobianGeneratorEvent
  have he : (⟨(machineCombWindow bs i).toNat % 16, Nat.mod_lt _ (by decide)⟩ : Fin 16) =
      ⟨combIndex (leValue bs) i, hb⟩ := by
    apply Fin.ext
    change (machineCombWindow bs i).toNat % 16 = combIndex (leValue bs) i
    rw [hv, Nat.mod_eq_of_lt hb]
  rw [he]
  have ht := builtinJacobian_rep ⟨combIndex (leValue bs) i, hb⟩
  rwa [builtinGenerator_multiples] at ht

def jacobianScalarEvents (ps : List JacobianScalarInput) (g : Option (List Byte))
    (i : ℕ) : List (Jacobian (ZMod p)) :=
  (match g with
    | none => []
    | some bs => if i < 99 then [jacobianGeneratorEvent bs i] else []) ++
  (if i % 5 = 0 then ps.map (fun q => jacobianOrdinaryEvent q i) else [])

def jacobianScalarValues (ps : List JacobianScalarInput) : List (ℕ × P384Point) :=
  ps.map (fun q => (leValue q.scalar, q.value))

def jacobianGeneratorValue (g : Option (List Byte)) : Option (ℕ × P384Point) :=
  g.map (fun bs => (leValue bs, builtinCurvePoint 1))

theorem jacobianScalarEvents_rep (ps : List JacobianScalarInput) (g : Option (List Byte))
    (hp : ∀ q ∈ ps, JacobianScalarValid q) (hg : ∀ bs, g = some bs → bs.length = 48)
    (i : ℕ) : List.Forall₂ (Represents (nistB : ZMod p)) (jacobianScalarEvents ps g i)
      (scalarEvents (jacobianScalarValues ps) (jacobianGeneratorValue g) i) := by
  unfold jacobianScalarEvents scalarEvents
  apply List.rel_append
  · cases g with
    | none => exact .nil
    | some bs =>
        change List.Forall₂ (Represents (nistB : ZMod p))
          (if i < 99 then [jacobianGeneratorEvent bs i] else [])
          (if i < 99 then [(combCoefficient (combIndex (leValue bs) i) : ℤ) • builtinCurvePoint 1] else [])
        by_cases hi : i < 99
        · rw [if_pos hi, if_pos hi]
          exact .cons (jacobianGeneratorEvent_rep bs (hg bs rfl) i) .nil
        · rw [if_neg hi, if_neg hi]
          exact .nil
  · unfold ordinaryEvents jacobianScalarValues
    by_cases hi : i % 5 = 0
    · rw [if_pos hi, if_pos hi]
      simp only [List.map_map, Function.comp_def]
      have he : i = 5 * (i / 5) := by omega
      induction ps with
      | nil => exact .nil
      | cons q ps ih =>
          apply List.Forall₂.cons
          · have hrow := jacobianOrdinaryEvent_rep q (hp q (by simp)) (i / 5)
            rw [← he] at hrow
            exact hrow
          · exact ih (fun r hr => hp r (by simp [hr]))
    · rw [if_neg hi, if_neg hi]
      exact .nil

def jacobianScalarMul (ps : List JacobianScalarInput) (g : Option (List Byte)) : Jacobian (ZMod p) :=
  (jacobianBatchLoop (jacobianScalarEvents ps g) (if ps.isEmpty then 99 else 381)
    ⟨jacobianZero, true⟩).acc

theorem jacobianScalarMul_correct (ps : List JacobianScalarInput) (g : Option (List Byte))
    (hp : ∀ q ∈ ps, JacobianScalarValid q) (hg : ∀ bs, g = some bs → bs.length = 48) :
    Represents (nistB : ZMod p) (jacobianScalarMul ps g)
      (generatorValue (jacobianGeneratorValue g) +
        (ps.map (fun q => (leValue q.scalar : ℤ) • q.value)).sum) := by
  have bound (bs : List Byte) (h : bs.length = 48) : leValue bs < 2^384 := by
    simpa [h] using leValue_bound bs
  have h := jacobianBatchLoop_scalar_correct (nistB : ZMod p) (jacobianScalarValues ps)
    (jacobianGeneratorValue g) (jacobianScalarEvents ps g) ?_ ?_ ?_ (by decide)
  · have he : (jacobianScalarValues ps).isEmpty = ps.isEmpty := by cases ps <;> rfl
    rw [he] at h
    simpa only [jacobianScalarValues, jacobianScalarMul,
      jacobianZero, List.map_map, Function.comp_def] using h
  · intro q hq
    rcases List.mem_map.mp hq with ⟨r, hr, rfl⟩
    exact bound r.scalar (hp r hr).1
  · cases g with
    | none => simp [jacobianGeneratorValue]
    | some bs =>
        intro q hq
        have he : (leValue bs, builtinCurvePoint 1) = q := by simpa [jacobianGeneratorValue] using hq
        rw [← he]
        exact bound bs (hg bs rfl)
  · intro i _
    exact jacobianScalarEvents_rep ps g hp hg i

end P384
