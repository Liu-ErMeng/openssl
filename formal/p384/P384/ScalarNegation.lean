import P384.ScalarWindows
import P384.Words
import P384.Inversion

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192
set_option exponentiation.threshold 2048

namespace P384

abbrev ScalarLimbWords := Fin 7 → BitVec 64

def scalarNegWords (a : ScalarLimbWords) : ScalarLimbWords :=
  fun i => BitVec.ofInt 64 (pad64 i) - a i

def scalarConditionalNeg (a : ScalarLimbWords) (sign : Byte) : ScalarLimbWords :=
  fun i => copyWord (a i) (scalarNegWords a i) (-(sign.setWidth 64))

theorem scalarNegWords_decode (a : ScalarLimbWords) :
    (fun i => unsigned (scalarNegWords a i)) = machineNeg (fun i => unsigned (a i)) := by
  funext i
  simp only [scalarNegWords, machineNeg, ofInt_unsigned]

theorem scalarSignMask (sign : BitVec 1) :
    -((sign.setWidth 8).setWidth 64) =
      if sign = 0 then (0 : BitVec 64) else BitVec.allOnes 64 := by
  revert sign
  decide

theorem scalarSignMask_byte (sign : Byte) (hs : sign.toNat ≤ 1) :
    -(sign.setWidth 64) = if sign = 0 then (0 : BitVec 64) else BitVec.allOnes 64 := by
  have h := scalarSignMask (sign.setWidth 1)
  rw [bitByte_roundtrip sign (by omega)] at h
  have he : (sign.setWidth 1 = 0) ↔ sign = 0 := by
    constructor
    · intro hz
      apply BitVec.eq_of_toNat_eq
      have ht := congrArg BitVec.toNat hz
      simpa only [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (show sign.toNat < 2 by omega)] using ht
    · intro hz
      subst sign
      rfl
  simpa only [he] using h

theorem scalarConditionalNeg_select (a : ScalarLimbWords) (sign : Byte) (hs : sign.toNat ≤ 1) :
    scalarConditionalNeg a sign = if sign = 0 then a else scalarNegWords a := by
  unfold scalarConditionalNeg
  rw [scalarSignMask_byte sign hs]
  by_cases he : sign = 0
  · rw [if_pos he, if_pos he]
    funext i
    exact copyWord_zero _ _
  · rw [if_neg he, if_neg he]
    funext i
    exact copyWord_ones _ _

theorem scalarNegWords_field (a : ScalarLimbWords)
    (ha : Reduced (fun i => unsigned (a i))) :
    fieldValue (fun i => unsigned (scalarNegWords a i)) =
      -fieldValue (fun i => unsigned (a i)) := by
  rw [scalarNegWords_decode]
  have h := (ZMod.intCast_eq_intCast_iff' _ _ p).2 (machineNeg_correct_reduced _ ha)
  simpa only [fieldValue, Int.cast_neg] using h

theorem scalarConditionalNeg_field (a : ScalarLimbWords) (sign : Byte) (hs : sign.toNat ≤ 1)
    (ha : Reduced (fun i => unsigned (a i))) :
    fieldValue (fun i => unsigned (scalarConditionalNeg a sign i)) =
      if sign = 0 then fieldValue (fun i => unsigned (a i)) else -fieldValue (fun i => unsigned (a i)) := by
  rw [scalarConditionalNeg_select a sign hs]
  by_cases he : sign = 0 <;> simp only [he, if_true, if_false]
  exact scalarNegWords_field a ha

theorem scalarNegWords_bound (a : ScalarLimbWords)
    (ha : Reduced (fun i => unsigned (a i))) :
    ∀ i, 0 ≤ unsigned (scalarNegWords a i) ∧ unsigned (scalarNegWords a i) ≤ pad64 i := by
  intro i
  rw [congrFun (scalarNegWords_decode a) i, machineNeg_refines _ (reduced_neg_no_underflow _ ha)]
  have hi := reduced_neg_no_underflow _ ha i
  change 0 ≤ pad64 i - unsigned (a i) ∧ pad64 i - unsigned (a i) ≤ pad64 i
  omega

theorem scalarConditionalNeg_bound (a : ScalarLimbWords) (sign : Byte) (hs : sign.toNat ≤ 1)
    (ha : Reduced (fun i => unsigned (a i))) :
    ∀ i, 0 ≤ unsigned (scalarConditionalNeg a sign i) ∧
      unsigned (scalarConditionalNeg a sign i) ≤ pad64 i := by
  rw [scalarConditionalNeg_select a sign hs]
  by_cases he : sign = 0
  · rw [if_pos he]
    exact reduced_neg_no_underflow _ ha
  · rw [if_neg he]
    exact scalarNegWords_bound a ha

theorem scalarSignedY_square_input (a z : ScalarLimbWords) (sign : Byte) (hs : sign.toNat ≤ 1)
    (ha : Reduced (fun i => unsigned (a i))) (hz : Reduced (fun i => unsigned (z i))) :
    ∀ i, Within 61 (unsigned (scalarConditionalNeg a sign i) + unsigned (z i)) := by
  intro i
  have hy := scalarConditionalNeg_bound a sign hs ha i
  have hzi := reduced_limbs_small _ hz i
  have hp : pad64 i < (2^60 + 2^45 : ℤ) := by fin_cases i <;> decide
  norm_num [Within] at hzi ⊢
  omega

end P384
