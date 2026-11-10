import P384.ScalarTable
import P384.ScalarNegation
import P384.Contract
import P384.ScalarOutput

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000
set_option exponentiation.threshold 2048

namespace P384

def scalarCounterexampleInputY : LimbWords := fun i =>
  BitVec.ofNat 64 ((generatorDoublingData 4).2 / 2^(56 * i.val) % 2^56)

def scalarCounterexampleNegY : LimbWords := scalarNegWords scalarCounterexampleInputY

def scalarCounterexampleContractY : Felem :=
  fun i => unsigned (machineContract scalarCounterexampleNegY i)

def scalarCounterexampleEncodedY : ℕ := leValue (felemBytes scalarCounterexampleContractY)

def scalarCounterexampleFixedY : Felem :=
  fun i => unsigned (machineContract (machineScalarOutputY scalarCounterexampleNegY) i)

def scalarCounterexampleFixedEncoding : ℕ := leValue (felemBytes scalarCounterexampleFixedY)

theorem scalarCounterexampleInputY_reduced :
    Reduced (fun i => unsigned (scalarCounterexampleInputY i)) := by
  unfold Reduced Within
  decide

theorem scalarCounterexampleInputY_value :
    eval7 (fun i => unsigned (scalarCounterexampleInputY i)) = ((generatorDoublingData 4).2 : ℤ) := by decide

theorem scalarCounterexampleNegY_correct :
    fieldValue (fun i => unsigned (scalarCounterexampleNegY i)) =
      -((generatorDoublingData 4).2 : ZMod p) := by
  rw [scalarCounterexampleNegY, scalarNegWords_field _ scalarCounterexampleInputY_reduced]
  simp only [fieldValue, scalarCounterexampleInputY_value, Int.cast_natCast]

theorem scalarCounterexampleNegY_not_reduced :
    ¬ Reduced (fun i => unsigned (scalarCounterexampleNegY i)) := by
  unfold Reduced Within
  decide

theorem scalarCounterexampleContractY_not_serial : ¬ serialFelem scalarCounterexampleContractY := by
  unfold serialFelem Within
  decide

theorem scalarCounterexampleEncodedY_incorrect :
    (scalarCounterexampleEncodedY : ZMod p) ≠ -((generatorDoublingData 4).2 : ZMod p) := by decide

theorem scalarCounterexampleEncodedY_value : scalarCounterexampleEncodedY =
    0x27eadd621ed6f92dbe7e92a1656bb70e2be2b03bf1d5c42463545a81bbf585442edef3460b640ddc88dd48ab1454c98c := by decide

theorem scalarCounterexampleEncodedY_off_curve :
    ((scalarCounterexampleEncodedY^2 + 3 * (generatorDoublingData 4).1) % p) ≠
      (((generatorDoublingData 4).1^3 + nistB) % p) := by decide

theorem scalarCounterexampleFixedY_serial : serialFelem scalarCounterexampleFixedY :=
  (machineScalarOutputY_contract scalarCounterexampleNegY).2

theorem scalarCounterexampleFixedEncoding_value : scalarCounterexampleFixedEncoding =
    0x27eadd621ed6f92dbe7e92a1656bb70e2be2b03bf1d5c42463545a81bbf585442edef3460b640ddc97dd48ab1454c98c := by decide

theorem scalarCounterexampleFixedEncoding_on_curve :
    (scalarCounterexampleFixedEncoding^2 + 3 * (generatorDoublingData 4).1) % p =
      ((generatorDoublingData 4).1^3 + nistB) % p := by decide

theorem scalarCounterexample_group_value :
    (32 : ℤ) • (-builtinCurvePoint 1) + (16 : ℤ) • builtinCurvePoint 1 =
      -generatorWitnessPoint 4 := by
  change (32 : ℤ) • (-builtinCurvePoint 1) + (16 : ℤ) • builtinCurvePoint 1 =
    -generatorWitnessPoint ⟨4, by decide⟩
  rw [generatorWitness_multiple 4 (by decide)]
  simp only [smul_neg, ← neg_zsmul, ← add_zsmul]
  norm_num
  have hh : (32 : ℤ) • builtinCurvePoint 1 =
      (16 : ℤ) • builtinCurvePoint 1 + (16 : ℤ) • builtinCurvePoint 1 := by
    rw [← add_zsmul]
    norm_num
  rw [hh]
  abel

end P384
