import P384.GeneratedProducts

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 16384

namespace P384

theorem widen_61 (x : ℤ) (hx : Within 61 x) :
    (BitVec.ofInt 64 x).setWidth 128 = BitVec.ofInt 128 x :=
  setWidth_ofInt_exact 64 128 x (within_mono hx (by decide)) (within_mono hx (by decide))

theorem double_widen_61 (x : ℤ) (hx : Within 61 x) :
    ((BitVec.ofInt 64 x * 2).setWidth 128) = BitVec.ofInt 128 (2 * x) := by
  have hd : BitVec.ofInt 64 x * 2 = BitVec.ofInt 64 (2 * x) := by
    rw [BitVec.mul_comm]
    exact (BitVec.ofInt_mul 2 x).symm
  rw [hd]
  have hb : Within 62 (2 * x) := by norm_num [Within] at *; omega
  exact setWidth_ofInt_exact 64 128 _ (within_mono hb (by decide)) (within_mono hb (by decide))

theorem machineMul_pack (a b : Felem)
    (ha : ∀ i, Within 61 (a i)) (hb : ∀ i, Within 61 (b i)) :
    machineMul (fun i => BitVec.ofInt 64 (a i)) (fun i => BitVec.ofInt 64 (b i)) =
      fun i => BitVec.ofInt 128 (mul a b i) := by
  have hA := fun i => widen_61 (a i) (ha i)
  have hB := fun i => widen_61 (b i) (hb i)
  funext i
  fin_cases i <;> simp only [machineMul, mul, Matrix.cons_val, hA, hB,
    ← BitVec.ofInt_add, ← BitVec.ofInt_mul] <;> rfl

theorem machineSquare_pack (a : Felem) (ha : ∀ i, Within 61 (a i)) :
    machineSquare (fun i => BitVec.ofInt 64 (a i)) = fun i => BitVec.ofInt 128 (square a i) := by
  have hA := fun i => widen_61 (a i) (ha i)
  have hD := fun i => double_widen_61 (a i) (ha i)
  funext i
  fin_cases i <;> simp only [machineSquare, square, Matrix.cons_val, hA, hD,
    ← BitVec.ofInt_add, ← BitVec.ofInt_mul] <;> rfl

theorem wide_bound_fits (x : ℤ) (hx : 0 ≤ x ∧ x < 2^128 - 2^125) : Within 128 x := by
  norm_num [Within] at *
  omega

theorem word_input_61 (a : LimbWords) (ha : ∀ i, unsigned (a i) < 2^61) :
    ∀ i, Within 61 (unsigned (a i)) := fun i => ⟨(unsigned_bounds (a i)).1, ha i⟩

theorem machineMul_refines (a b : LimbWords)
    (ha : ∀ i, unsigned (a i) < 2^61) (hb : ∀ i, unsigned (b i) < 2^61) :
    (fun i => unsigned (machineMul a b i)) = mul (fun i => unsigned (a i)) (fun i => unsigned (b i)) := by
  have hA := word_input_61 a ha
  have hB := word_input_61 b hb
  have heA : (fun i => BitVec.ofInt 64 (unsigned (a i))) = a := funext fun i => ofInt_unsigned (a i)
  have heB : (fun i => BitVec.ofInt 64 (unsigned (b i))) = b := funext fun i => ofInt_unsigned (b i)
  have hm := machineMul_pack _ _ hA hB
  rw [heA, heB] at hm
  funext i
  rw [congrFun hm i]
  exact unsigned_ofInt_exact 128 _ (wide_bound_fits _ (mul_bounds _ _ hA hB i))

theorem machineSquare_refines (a : LimbWords) (ha : ∀ i, unsigned (a i) < 2^61) :
    (fun i => unsigned (machineSquare a i)) = square (fun i => unsigned (a i)) := by
  have hA := word_input_61 a ha
  have heA : (fun i => BitVec.ofInt 64 (unsigned (a i))) = a := funext fun i => ofInt_unsigned (a i)
  have hm := machineSquare_pack _ hA
  rw [heA] at hm
  funext i
  rw [congrFun hm i]
  exact unsigned_ofInt_exact 128 _ (wide_bound_fits _ (square_bounds _ hA i))

def machineMulReduce (a b : LimbWords) : LimbWords := machineReduce (machineMul a b)
def machineSquareReduce (a : LimbWords) : LimbWords := machineReduce (machineSquare a)

theorem machineMulReduce_correct (a b : LimbWords)
    (ha : ∀ i, unsigned (a i) < 2^61) (hb : ∀ i, unsigned (b i) < 2^61) :
    Congruent (eval7 (fun i => unsigned (machineMulReduce a b i)))
      (eval7 (fun i => unsigned (a i)) * eval7 (fun i => unsigned (b i))) ∧
      Reduced (fun i => unsigned (machineMulReduce a b i)) := by
  have hm := machineMul_refines a b ha hb
  have hbound := mul_bounds _ _ (word_input_61 a ha) (word_input_61 b hb)
  have hi : ∀ i, unsigned (machineMul a b i) < 2^128 - 2^125 := by
    intro i
    rw [congrFun hm i]
    exact (hbound i).2
  have hc := machineReduce_correct (machineMul a b) hi
  rw [hm, mul_correct] at hc
  exact hc

theorem machineSquareReduce_correct (a : LimbWords) (ha : ∀ i, unsigned (a i) < 2^61) :
    Congruent (eval7 (fun i => unsigned (machineSquareReduce a i)))
      (eval7 (fun i => unsigned (a i))^2) ∧
      Reduced (fun i => unsigned (machineSquareReduce a i)) := by
  have hm := machineSquare_refines a ha
  have hbound := square_bounds _ (word_input_61 a ha)
  have hi : ∀ i, unsigned (machineSquare a i) < 2^128 - 2^125 := by
    intro i
    rw [congrFun hm i]
    exact (hbound i).2
  have hc := machineReduce_correct (machineSquare a) hi
  rw [hm, square_correct] at hc
  exact hc

end P384
