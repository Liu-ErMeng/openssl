import P384.ScalarCurve
import P384.GeneratedGeneratorWitness

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 32000000
set_option exponentiation.threshold 2048

namespace P384

def generatorWitnessJacobian (idx : Fin 286) : Jacobian (ZMod p) :=
  ⟨(generatorDoublingData idx).1, (generatorDoublingData idx).2, 1⟩

theorem generatorWitness_curve : ∀ idx : Fin 286,
    ((generatorDoublingData idx).2^2 + 3 * (generatorDoublingData idx).1) % p =
      ((generatorDoublingData idx).1^3 + nistB) % p ∧
    (2 * (generatorDoublingData idx).2) % p ≠ 0 := by decide

def generatorWitnessPoint (idx : Fin 286) : P384Point :=
  WeierstrassCurve.Affine.Point.some (natCurvePoint_nonsingular _ _
    (generatorWitness_curve idx).1 (generatorWitness_curve idx).2)

theorem generatorWitness_rep (idx : Fin 286) :
    Represents (nistB : ZMod p) (generatorWitnessJacobian idx) (generatorWitnessPoint idx) := by
  constructor
  · exact one_ne_zero
  · simp [generatorWitnessJacobian, affine]

theorem generatorWitness_double_certificate : ∀ idx : Fin 285,
    let q := pointDouble (generatorWitnessJacobian idx.castSucc)
    q.z ≠ 0 ∧ q.x = ((generatorDoublingData idx.succ).1 : ZMod p) * q.z^2 ∧
      q.y = ((generatorDoublingData idx.succ).2 : ZMod p) * q.z^3 := by decide

theorem generatorWitness_double (idx : Fin 285) :
    generatorWitnessPoint idx.succ =
      generatorWitnessPoint idx.castSucc + generatorWitnessPoint idx.castSucc := by
  have hc := generatorWitness_double_certificate idx
  have hp := represents_scaled (nistB : ZMod p) (pointDouble (generatorWitnessJacobian idx.castSucc))
    _ _ (natCurvePoint_nonsingular _ _ (generatorWitness_curve idx.succ).1
      (generatorWitness_curve idx.succ).2) hc.1 hc.2.1 hc.2.2
  have hq := represents_double (nistB : ZMod p) _ _ (generatorWitness_rep idx.castSucc)
    (by decide)
  exact represents_functional _ _ _ _ hp hq

theorem generatorWitness_start : generatorWitnessPoint 0 = builtinCurvePoint 1 := by rfl

theorem generatorWitness_multiple (i : ℕ) (hi : i < 286) :
    generatorWitnessPoint ⟨i, hi⟩ = (2 : ℤ)^i • builtinCurvePoint 1 := by
  induction i with
  | zero => simpa using generatorWitness_start
  | succ i ih =>
      have he := generatorWitness_double ⟨i, by omega⟩
      change generatorWitnessPoint ⟨i + 1, hi⟩ =
        generatorWitnessPoint ⟨i, by omega⟩ + generatorWitnessPoint ⟨i, by omega⟩ at he
      rw [he, ih (by omega), pow_succ, mul_smul]
      simp only [show (2 : ℤ) = 1 + 1 from rfl, add_smul, one_smul, zsmul_add]

def builtinJacobian (idx : Fin 16) : Jacobian (ZMod p) :=
  ⟨builtinCoordinateNat idx 0, builtinCoordinateNat idx 1, builtinCoordinateNat idx 2⟩

theorem builtinJacobian_rep (idx : Fin 16) :
    Represents (nistB : ZMod p) (builtinJacobian idx) (builtinCurvePoint idx) := by
  unfold builtinCurvePoint
  split
  · rename_i hi
    have he : idx = 0 := Fin.ext hi
    subst idx
    change (builtinCoordinateNat 0 2 : ZMod p) = 0
    rw [builtin_zero]
    rfl
  · rename_i hi
    have hid : (⟨idx.val - 1, by omega⟩ : Fin 15).succ = idx := Fin.ext (by dsimp; omega)
    have hz : builtinCoordinateNat idx 2 = 1 := by rw [← hid]; exact builtin_affine_z _
    constructor
    · simpa only [builtinJacobian, hz, Nat.cast_one] using (one_ne_zero : (1 : ZMod p) ≠ 0)
    · simp only [builtinJacobian, affine, hz, Nat.cast_one, one_pow, div_one, hid]

def builtinHighBit : Fin 15 → ℕ := ![0, 1, 1, 2, 2, 2, 2, 3, 3, 3, 3, 3, 3, 3, 3]

def builtinParent (idx : Fin 15) : Fin 16 := ⟨idx.val + 1 - 2^(builtinHighBit idx), by
  have h : ∀ j : Fin 15, j.val + 1 - 2^(builtinHighBit j) < 16 := by decide
  exact h idx⟩

def builtinPower (idx : Fin 15) : Fin 286 := ⟨95 * builtinHighBit idx, by
  have h : ∀ j : Fin 15, 95 * builtinHighBit j < 286 := by decide
  exact h idx⟩

theorem builtin_table_certificate : ∀ idx : Fin 15,
    let q := pointAdd (builtinJacobian (builtinParent idx)) (generatorWitnessJacobian (builtinPower idx))
    q.z ≠ 0 ∧ q.x = (builtinCoordinateNat idx.succ 0 : ZMod p) * q.z^2 ∧
      q.y = (builtinCoordinateNat idx.succ 1 : ZMod p) * q.z^3 := by decide

theorem builtin_table_step (idx : Fin 15) : builtinCurvePoint idx.succ =
    builtinCurvePoint (builtinParent idx) + generatorWitnessPoint (builtinPower idx) := by
  have hc := builtin_table_certificate idx
  have hp := represents_scaled (nistB : ZMod p)
    (pointAdd (builtinJacobian (builtinParent idx)) (generatorWitnessJacobian (builtinPower idx)))
    _ _ (builtin_nonsingular idx) hc.1 hc.2.1 hc.2.2
  have hq := represents_add (nistB : ZMod p) _ _ _ _ (builtinJacobian_rep (builtinParent idx))
    (generatorWitness_rep (builtinPower idx)) (by decide)
  have he := represents_functional _ _ _ _ hp hq
  have hidx : idx.val + 1 ≠ 0 := by omega
  simpa only [builtinCurvePoint, dif_neg hidx] using he

theorem builtin_coefficient_split : ∀ idx : Fin 15,
    combCoefficient idx.succ.val = combCoefficient (builtinParent idx).val + 2^(builtinPower idx).val := by decide

theorem builtinParent_lt : ∀ idx : Fin 15, (builtinParent idx).val < idx.succ.val := by decide

theorem builtinGenerator_multiples (idx : Fin 16) :
    builtinCurvePoint idx = (combCoefficient idx.val : ℤ) • builtinCurvePoint 1 := by
  have h (i : ℕ) : ∀ hi : i < 16, builtinCurvePoint ⟨i, hi⟩ =
      (combCoefficient i : ℤ) • builtinCurvePoint 1 := by
    induction i using Nat.strong_induction_on with
    | h i ih =>
        intro hi
        cases i with
        | zero => simp [builtinCurvePoint, combCoefficient]
        | succ i =>
            let j : Fin 15 := ⟨i, by omega⟩
            have hs := builtin_table_step j
            change builtinCurvePoint ⟨i + 1, hi⟩ = _ at hs
            rw [hs, ih (builtinParent j).val (builtinParent_lt j) (builtinParent j).isLt,
              generatorWitness_multiple, ← add_zsmul]
            congr 1
            exact_mod_cast (builtin_coefficient_split j).symm
  exact h idx.val idx.isLt

end P384
