import P384.GeneratedScalarOutput
import P384.FieldInterfaces
import P384.ScalarNegation

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 16384
set_option exponentiation.threshold 2048

namespace P384

theorem scalarOutput_widen (x : BitVec 64) : unsigned (x.setWidth 128) = unsigned x := by
  rw [unsigned_setWidth]
  exact Int.emod_eq_of_lt (unsigned_bounds x).1 ((within_mono (unsigned_bounds x) (by decide) : Within 128 (unsigned x)).2)

theorem scalarOutputWide_bound (a : LimbWords) :
    ∀ i, unsigned (scalarOutputWide a i) < 297747071055821155530452781502797185024 := by
  have hb (j : Fin 7) : unsigned ((a j).setWidth 128) < 297747071055821155530452781502797185024 := by
    rw [scalarOutput_widen]
    have h := (unsigned_bounds (a j)).2
    norm_num at h ⊢
    omega
  intro i
  fin_cases i <;> simp only [scalarOutputWide, Matrix.cons_val_zero', Matrix.cons_val_succ']
  all_goals first | decide | exact hb _

theorem scalarOutputWide_value (a : LimbWords) :
    eval13 (fun i => unsigned (scalarOutputWide a i)) = eval7 (fun i => unsigned (a i)) := by
  simp only [eval13, eval7, scalarOutputWide, Matrix.cons_val, scalarOutput_widen,
    show unsigned (0 : BitVec 128) = 0 from rfl, zero_mul, add_zero]

theorem machineScalarOutputY_correct (a : LimbWords) :
    Congruent (eval7 (fun i => unsigned (machineScalarOutputY a i)))
      (eval7 (fun i => unsigned (a i))) ∧ Reduced (fun i => unsigned (machineScalarOutputY a i)) := by
  have h := machineReduce_correct (scalarOutputWide a) (scalarOutputWide_bound a)
  rw [scalarOutputWide_value] at h
  exact h

theorem machineScalarOutputY_field (a : LimbWords) :
    wordField (machineScalarOutputY a) = wordField a := by
  exact (ZMod.intCast_eq_intCast_iff' _ _ p).2 (machineScalarOutputY_correct a).1

theorem machineScalarOutputY_contract (a : LimbWords) :
    eval7 (fun i => unsigned (machineContract (machineScalarOutputY a) i)) =
      eval7 (fun i => unsigned (a i)) % (p : ℤ) ∧
    serialFelem (fun i => unsigned (machineContract (machineScalarOutputY a) i)) := by
  have h := machineContract_correct (machineScalarOutputY a) (machineScalarOutputY_correct a).2
  rw [(machineScalarOutputY_correct a).1] at h
  exact h

theorem machineScalarOutputY_to_bn (mem : ByteMemory) (off : ℕ) (a : LimbWords) :
    (bnWordValue (canonicalBNWords mem off (machineScalarOutputY a)) : ℤ) =
      eval7 (fun i => unsigned (a i)) % (p : ℤ) := by
  rw [canonicalBNWords_value _ _ _ (machineScalarOutputY_correct a).2]
  exact (machineScalarOutputY_correct a).1

theorem machineScalarOutputY_neg_to_bn (mem : ByteMemory) (off : ℕ) (a : LimbWords)
    (ha : Reduced (fun i => unsigned (a i))) :
    (bnWordValue (canonicalBNWords mem off (machineScalarOutputY (scalarNegWords a))) : ZMod p) =
      -wordField a := by
  rw [canonicalBNWords_field _ _ _ (machineScalarOutputY_correct _).2, machineScalarOutputY_field]
  exact scalarNegWords_field a ha

end P384
