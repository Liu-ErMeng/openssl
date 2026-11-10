import P384.Carry
import P384.GeneratedContract

set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option exponentiation.threshold 2048

namespace P384

theorem carryTerms_signed (a : Felem)
    (ha : ∀ i, -2^57 ≤ a i ∧ a i < 2^57) :
    ∀ i : Fin 6, Signed64 (carryTerms a i.succ) := by
  have h0 := ha 0
  have h1 := ha 1
  have h2 := ha 2
  have h3 := ha 3
  have h4 := ha 4
  have h5 := ha 5
  have h6 := ha 6
  let t0 := a 0
  let t1 := a 1 + t0 / radix
  let t2 := a 2 + t1 / radix
  let t3 := a 3 + t2 / radix
  let t4 := a 4 + t3 / radix
  let t5 := a 5 + t4 / radix
  let t6 := a 6 + t5 / radix
  intro i
  fin_cases i
  · change Signed64 t1
    dsimp only [t1, t0]
    norm_num [Signed64, radix] at *
    omega
  · change Signed64 t2
    dsimp only [t2, t1, t0]
    norm_num [Signed64, radix] at *
    omega
  · change Signed64 t3
    dsimp only [t3, t2, t1, t0]
    norm_num [Signed64, radix] at *
    omega
  · change Signed64 t4
    dsimp only [t4, t3, t2, t1, t0]
    norm_num [Signed64, radix] at *
    omega
  · change Signed64 t5
    dsimp only [t5, t4, t3, t2, t1, t0]
    norm_num [Signed64, radix] at *
    omega
  · change Signed64 t6
    dsimp only [t6, t5, t4, t3, t2, t1, t0]
    norm_num [Signed64, radix] at *
    omega

theorem machineContractCarry_pack (a : Felem)
    (h0 : -2^32 ≤ a 0 ∧ a 0 < 2^56)
    (ha : ∀ i, -2^57 ≤ a i ∧ a i < 2^57) :
    (machineContractCarryTrace (fun i => BitVec.ofInt 64 (a i))).limbs =
      fun i => BitVec.ofInt 64 (carry7 a i) := by
  let q0 := a 0 / radix
  let t1 := a 1 + q0
  let t2 := a 2 + t1 / radix
  let t3 := a 3 + t2 / radix
  let t4 := a 4 + t3 / radix
  let t5 := a 5 + t4 / radix
  have hq : q0 = -1 ∨ q0 = 0 := by dsimp only [q0]; norm_num [radix] at h0 ⊢; omega
  have hb := borrow_shift63 (a 0) h0
  change (BitVec.ofInt 64 (a 0)).sshiftRight 63 = BitVec.ofInt 64 q0 at hb
  have hbm := borrow_mask q0 hq 56
  have hb1 := borrow_mask q0 hq 0
  change BitVec.ofInt 64 q0 &&& (72057594037927936 : BitVec 64) = BitVec.ofInt 64 (-q0 * radix) at hbm
  change BitVec.ofInt 64 q0 &&& (1 : BitVec 64) = BitVec.ofInt 64 (-q0 * 1) at hb1
  have hc0 : BitVec.ofInt 64 (a 0) + (BitVec.ofInt 64 q0 &&& (72057594037927936 : BitVec 64)) =
      BitVec.ofInt 64 (a 0 % radix) := by
    rw [hbm, ← BitVec.ofInt_add]
    congr 1
    rw [Int.emod_def]
    ring
  have hc1 : BitVec.ofInt 64 (a 1) - (BitVec.ofInt 64 q0 &&& (1 : BitVec 64)) = BitVec.ofInt 64 t1 := by
    rw [hb1, ofInt_sub]
    congr 1
    dsimp only [t1]
    ring
  have hs (i : Fin 6) : (BitVec.ofInt 64 (carryTerms a i.succ)).sshiftRight 56 =
      BitVec.ofInt 64 (carryTerms a i.succ / radix) := ofInt_sshiftRight _ (carryTerms_signed a ha i) 56
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
  have he12 : a 2 + t1 / radix = t2 := rfl
  have he23 : a 3 + t2 / radix = t3 := rfl
  have he34 : a 4 + t3 / radix = t4 := rfl
  have he45 : a 5 + t4 / radix = t5 := rfl
  have hm (x : ℤ) : BitVec.ofInt 64 x &&& (72057594037927935 : BitVec 64) =
      BitVec.ofInt 64 (x % radix) := ofInt_mask_any x 56 (by decide)
  dsimp only [machineContractCarryTrace]
  simp only [hb, hc0, hc1, hs1, hs2, hs3, hs4, hs5, ← BitVec.ofInt_add,
    he12, he23, he34, he45, hm]
  funext i
  fin_cases i <;> rfl

end P384
