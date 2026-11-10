import P384.Carry
import P384.GeneratedContract

set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 16384
set_option exponentiation.threshold 2048

namespace P384

theorem machineContractFirst_pack (a : Felem) (ha : Reduced a) :
    machineContractFirst (fun i => BitVec.ofInt 64 (a i)) =
      fun i => BitVec.ofInt 64 (contractFirst a i) := by
  have h6 := reduced_limbs_small a ha 6
  have hh : (BitVec.ofInt 64 (a 6)) >>> 48 = BitVec.ofInt 64 (contractHighBit a) :=
    ofInt_shiftRight 64 _ (within_mono h6 (by decide)) 48
  have h0 := contractFold_zero_bounds a ha
  have hq : contractFold a 0 / radix = -1 ∨ contractFold a 0 / radix = 0 := by
    norm_num [radix] at h0 ⊢
    omega
  have hb := borrow_shift63 (contractFold a 0) h0
  have hbm := borrow_mask _ hq 56
  have hb1 := borrow_mask _ hq 0
  have hmask (x : ℤ) : BitVec.ofInt 64 x &&& (72057594037927935 : BitVec 64) =
      BitVec.ofInt 64 (x % radix) := ofInt_mask_any x 56 (by decide)
  have htmask : BitVec.ofInt 64 (a 6) &&& (281474976710655 : BitVec 64) =
      BitVec.ofInt 64 (a 6 % 2^48) := ofInt_mask_any _ 48 (by decide)
  have hs (i : Fin 6) :
      (BitVec.ofInt 64 (carryTerms (contractFold a) i.succ)).sshiftRight 56 =
        BitVec.ofInt 64 (carryTerms (contractFold a) i.succ / radix) := by
    apply ofInt_sshiftRight
    have h := contractCarryTerms_bounds a ha i
    norm_num [Within, Signed64] at h ⊢
    omega
  let bit := contractHighBit a
  let f0 := a 0 + bit - bit * 2^32
  let f1 := a 1 + bit * 2^40
  let f2 := a 2 + bit * 2^16
  let q0 := f0 / radix
  let t1 := f1 + q0
  let t2 := f2 + t1 / radix
  let t3 := a 3 + t2 / radix
  let t4 := a 4 + t3 / radix
  let t5 := a 5 + t4 / radix
  change (BitVec.ofInt 64 f0).sshiftRight 63 = BitVec.ofInt 64 q0 at hb
  change BitVec.ofInt 64 q0 &&& (72057594037927936 : BitVec 64) =
    BitVec.ofInt 64 (-q0 * radix) at hbm
  change BitVec.ofInt 64 q0 &&& (1 : BitVec 64) = BitVec.ofInt 64 (-q0 * 1) at hb1
  have hc0 : BitVec.ofInt 64 f0 + (BitVec.ofInt 64 q0 &&& (72057594037927936 : BitVec 64)) =
      BitVec.ofInt 64 (f0 % radix) := by
    rw [hbm, ← BitVec.ofInt_add]
    congr 1
    rw [Int.emod_def]
    ring
  have hc1 : BitVec.ofInt 64 f1 - (BitVec.ofInt 64 q0 &&& (1 : BitVec 64)) =
      BitVec.ofInt 64 t1 := by
    rw [hb1, ofInt_sub]
    congr 1
    dsimp only [t1]
    ring
  have hs1 := hs 0
  have hs2 := hs 1
  have hs3 := hs 2
  have hs4 := hs 3
  have hs5 := hs 4
  change (BitVec.ofInt 64 t1).sshiftRight 56 = BitVec.ofInt 64 (t1 / radix) at hs1
  change (BitVec.ofInt 64 t2).sshiftRight 56 = BitVec.ofInt 64 (t2 / radix) at hs2
  change (BitVec.ofInt 64 t3).sshiftRight 56 = BitVec.ofInt 64 (t3 / radix) at hs3
  change (BitVec.ofInt 64 t4).sshiftRight 56 = BitVec.ofInt 64 (t4 / radix) at hs4
  change (BitVec.ofInt 64 t5).sshiftRight 56 = BitVec.ofInt 64 (t5 / radix) at hs5
  have he0 : (a 0 + contractHighBit a) - contractHighBit a * 2^32 = f0 := rfl
  have he1 : a 1 + contractHighBit a * 2^40 = f1 := rfl
  have he2 : a 2 + contractHighBit a * 2^16 = f2 := rfl
  have he12 : f2 + t1 / radix = t2 := rfl
  have he23 : a 3 + t2 / radix = t3 := rfl
  have he34 : a 4 + t3 / radix = t4 := rfl
  have he45 : a 5 + t4 / radix = t5 := rfl
  dsimp only [machineContractFirst, machineContractFirstTrace]
  simp only [hh, ofInt_shiftLeft, ← BitVec.ofInt_add, ofInt_sub,
    he0, he1, he2, htmask, hb, hc0, hc1, hs1, hs2, hs3, hs4, hs5,
    he12, he23, he34, he45, hmask]
  funext i
  fin_cases i <;> rfl

theorem machineContractFirst_refines (a : LimbWords)
    (ha : Reduced (fun i => unsigned (a i))) :
    (fun i => unsigned (machineContractFirst a i)) = contractFirst (fun i => unsigned (a i)) := by
  have he := machineContractFirst_pack (fun i => unsigned (a i)) ha
  have hin : (fun i => BitVec.ofInt 64 (unsigned (a i))) = a := by
    funext i
    exact ofInt_unsigned _
  rw [hin] at he
  have hb := (contractFirst_correct _ ha).2
  funext i
  rw [congrFun he i]
  exact unsigned_ofInt_exact 64 _ (within_mono (serialFelem_limb_bound _ hb i) (by decide))

theorem machineContractFirst_correct (a : LimbWords)
    (ha : Reduced (fun i => unsigned (a i))) :
    Congruent (eval7 (fun i => unsigned (machineContractFirst a i)))
      (eval7 (fun i => unsigned (a i))) ∧
    serialFelem (fun i => unsigned (machineContractFirst a i)) := by
  rw [machineContractFirst_refines a ha]
  exact contractFirst_correct _ ha

end P384
