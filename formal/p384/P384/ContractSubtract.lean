import P384.ContractArithmetic
import P384.ContractGates

set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 16384
set_option exponentiation.threshold 2048

namespace P384

open Classical

theorem and_bit16_zero (x : BitVec 64) (h : ¬unsigned x / 2^16 % 2 = 1) :
    x &&& (65536 : BitVec 64) = 0 := by
  have hn : ¬x.toNat / 2^16 % 2 = 1 := by
    intro he
    apply h
    unfold unsigned
    exact_mod_cast he
  change x &&& BitVec.twoPow 64 16 = 0
  rw [BitVec.and_twoPow]
  have hb : x.getLsbD 16 = false := by
    change x.toNat.testBit 16 = false
    rw [Nat.testBit_to_div_mod]
    have hh : x.toNat / 2^16 % 2 = 0 := by omega
    simp only [hh]
    rfl
  rw [hb]
  rfl

theorem contractSubtract_pack (a : Felem) (ha : serialFelem a) :
    (machineContractSubtractTrace (fun i => BitVec.ofInt 64 (a i))).limbs =
      fun i => BitVec.ofInt 64 (contractSubtract a i) := by
  let input : LimbWords := fun i => BitVec.ofInt 64 (a i)
  have hin : (fun i => unsigned (input i)) = a := by
    funext i
    exact unsigned_ofInt_exact 64 _ (within_mono (serialFelem_limb_bound a ha i) (by decide))
  have hm := contractMainGate_correct input (by rw [hin]; exact ha)
  have hb := contractBitGate_correct input (by rw [hin]; exact ha)
  have ho := contractOtherGate_correct input (by rw [hin]; exact ha)
  rw [hin] at hm hb ho
  unfold contractMainGate at hm
  unfold contractBitGate at hb
  unfold contractOtherGate at ho
  have h16 (x : BitVec 64) : (x &&& (131071 : BitVec 64)) &&& (72057594037862399 : BitVec 64) =
      x &&& (65535 : BitVec 64) := by rw [BitVec.and_assoc]; rfl
  have hbit (x : BitVec 64) : (x &&& (131071 : BitVec 64)) &&& (72057594037862400 : BitVec 64) =
      x &&& (65536 : BitVec 64) := by rw [BitVec.and_assoc]; rfl
  have hmask16 : input 2 &&& (65535 : BitVec 64) = BitVec.ofInt 64 (a 2 % 2^16) :=
    ofInt_mask_any _ 16 (by decide)
  have hmask40 : input 1 &&& (1099511627775 : BitVec 64) = BitVec.ofInt 64 (a 1 % 2^40) :=
    ofInt_mask_any _ 40 (by decide)
  have hp40 : (1 : BitVec 64) <<< 40 = BitVec.ofInt 64 (2^40) := by decide
  have hneg : -((1 : BitVec 64) <<< 32) + 1 = BitVec.ofInt 64 (-2^32 + 1) := by decide
  have hsum0 : input 0 + BitVec.ofInt 64 (-2^32 + 1) = BitVec.ofInt 64 (a 0 - 2^32 + 1) := by
    rw [← BitVec.ofInt_add]
    congr 1
    ring
  have hsum1 : input 1 + BitVec.ofInt 64 (2^40) = BitVec.ofInt 64 (a 1 + 2^40) :=
    (BitVec.ofInt_add _ _).symm
  have hnot0 : ~~~(0 : BitVec 64) = BitVec.allOnes 64 := by decide
  have hzeroAnd (x : BitVec 64) : (0 : BitVec 64) &&& x = 0 := BitVec.zero_and
  have hadd0 (x : BitVec 64) : x + (0 : BitVec 64) = x := BitVec.add_zero x
  change (machineContractSubtractTrace input).limbs = _
  dsimp only [machineContractSubtractTrace]
  rw [hm, hb, ho]
  by_cases hs : contractNeedsSubtract a
  · by_cases ht : contractPredicates a 1
    · simp only [wordFlag, hs, ht, not_true_eq_false, and_self, and_false, ↓reduceIte]
      simp only [BitVec.not_allOnes, hnot0, BitVec.zero_or, BitVec.or_allOnes, BitVec.allOnes_or,
        BitVec.and_allOnes, BitVec.allOnes_and, BitVec.and_zero, BitVec.zero_and,
        BitVec.add_zero, hzeroAnd, hadd0, h16, hmask16, hp40, hneg, hsum0, hsum1]
      funext i
      fin_cases i <;> simp only [contractSubtract, if_pos hs, if_pos ht] <;> rfl
    · have hz : input 2 &&& (65536 : BitVec 64) = 0 := by
        apply and_bit16_zero
        have hu := congrFun hin 2
        rw [hu]
        exact ht
      simp only [wordFlag, hs, ht, not_false_eq_true, false_and, and_false, and_true, true_and, ↓reduceIte]
      simp only [BitVec.not_allOnes, hnot0, BitVec.zero_or, BitVec.or_allOnes, BitVec.allOnes_or,
        BitVec.and_allOnes, BitVec.allOnes_and, BitVec.and_zero, BitVec.zero_and,
        BitVec.add_zero, hzeroAnd, hadd0, hbit, hz, hmask40, hp40, hneg, hsum0]
      funext i
      fin_cases i <;> simp only [contractSubtract, if_pos hs, if_neg ht] <;> rfl
  · simp only [wordFlag, hs, false_and, ↓reduceIte]
    (try simp only [hnot0, BitVec.or_allOnes, BitVec.allOnes_or, BitVec.and_allOnes, BitVec.and_zero,
      BitVec.zero_and, BitVec.add_zero, hzeroAnd, hadd0])
    funext i
    fin_cases i <;> simp only [contractSubtract, if_neg hs] <;> rfl

end P384
