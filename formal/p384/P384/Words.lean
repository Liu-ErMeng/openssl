import P384.Basic

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

namespace P384

def copyWord (out input mask : BitVec 64) : BitVec 64 :=
  out ^^^ (mask &&& (input ^^^ out))

theorem copyWord_zero (out input : BitVec 64) : copyWord out input 0 = out := by
  simp [copyWord]

theorem copyWord_ones (out input : BitVec 64) :
    copyWord out input (BitVec.allOnes 64) = input := by
  rw [copyWord, BitVec.allOnes_and, BitVec.xor_comm input out,
    ← BitVec.xor_assoc, BitVec.xor_self, BitVec.zero_xor]

def selectionMask (i idx : BitVec 64) : BitVec 64 :=
  let mask := i ^^^ idx
  let mask := mask ||| (mask >>> 4)
  let mask := mask ||| (mask >>> 2)
  let mask := mask ||| (mask >>> 1)
  (mask &&& 1) - 1

theorem selectionMask_correct (i idx : BitVec 5) :
    selectionMask (i.zeroExtend 64) (idx.zeroExtend 64) =
      if i = idx then BitVec.allOnes 64 else 0 := by
  revert i idx
  decide

def zeroMask (x : BitVec 64) : BitVec 64 := (x - 1).sshiftRight 63

theorem zeroMask_correct (x : BitVec 63) :
    zeroMask (x.zeroExtend 64) = if x = 0 then BitVec.allOnes 64 else 0 := by
  by_cases hx : x = 0
  · subst x
    decide
  · rw [if_neg hx]
    have hpos : 0 < x.toNat := by
      have hne : x.toNat ≠ 0 := by
        intro h
        exact hx (BitVec.eq_of_toNat_eq h)
      omega
    have hlt := x.isLt
    have hext : (x.zeroExtend 64).toNat = x.toNat := by
      simp only [BitVec.zeroExtend_eq_setWidth, BitVec.toNat_setWidth]
      apply Nat.mod_eq_of_lt
      omega
    have hsub : (x.zeroExtend 64 - 1).toNat = x.toNat - 1 := by
      rw [BitVec.toNat_sub, hext]
      change ((2^64 - 1 + x.toNat) % 2^64) = x.toNat - 1
      omega
    have hmsb : (x.zeroExtend 64 - 1).msb = false := by
      rw [BitVec.msb_eq_false_iff_two_mul_lt, hsub]
      norm_num at hlt ⊢
      omega
    unfold zeroMask
    rw [BitVec.sshiftRight_eq_of_msb_false hmsb]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_ushiftRight, hsub, Nat.shiftRight_eq_div_pow]
    change (x.toNat - 1) / 2^63 = 0
    apply Nat.div_eq_of_lt
    omega

end P384
