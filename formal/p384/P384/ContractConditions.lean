import P384.BitSlices
import P384.ContractCompare
import P384.GeneratedContract
import P384.ZeroRefinement

set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 16384
set_option exponentiation.threshold 2048

namespace P384

open Classical

theorem contractMask_correct (x : BitVec 64) :
    zeroMask (x &&& (72057594037927935 : BitVec 64)) =
      if x.setWidth 56 = 0 then BitVec.allOnes 64 else 0 := by
  have hb : unsigned (x &&& (72057594037927935 : BitVec 64)) < 2^63 := by
    rw [show (72057594037927935 : BitVec 64) = BitVec.ofNat 64 (2^56 - 1) from rfl,
      unsigned_mask x 56 (by decide)]
    have hr := Int.emod_lt_of_pos (unsigned x) (by norm_num : (0 : ℤ) < 2^56)
    norm_num at hr ⊢
    omega
  have hz : x &&& (72057594037927935 : BitVec 64) = 0 ↔ x.setWidth 56 = 0 := by
    rw [BitVec.toNat_eq, BitVec.toNat_eq]
    change (x &&& BitVec.ofNat 64 (2^56 - 1)).toNat = 0 ↔ (x.setWidth 56).toNat = 0
    rw [lowMask_toNat x 56 (by decide), BitVec.toNat_setWidth]
  rw [zeroMask_bounded _ hb]
  simp only [hz]

theorem contractMask_succ (x : BitVec 64) :
    zeroMask ((x + 1) &&& (72057594037927935 : BitVec 64)) =
      if x.setWidth 56 = BitVec.allOnes 56 then BitVec.allOnes 64 else 0 := by
  rw [contractMask_correct, BitVec.setWidth_add _ _ (by decide)]
  have hone : (1 : BitVec 64).setWidth 56 = (1 : BitVec 56) := by decide
  simp only [hone, succ56_zero]

theorem machineContractConditions_correct (a : LimbWords)
    (ha : serialFelem (fun i => unsigned (a i))) :
    (machineContractConditionsTrace a).conditions = fun i =>
      if contractPredicates (fun j => unsigned (a j)) i then BitVec.allOnes 64 else 0 := by
  have hsmall (i : Fin 7) : (a i).toNat < 2^56 := by
    have h := serialFelem_limb_bound _ ha i
    have hh := h.2
    change ((a i).toNat : ℤ) < 2^56 at hh
    exact_mod_cast hh
  have hlow (i : Fin 7) : ((a i).setWidth 56).toNat = (a i).toNat := by
    rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (hsmall i)]
  have htop : (a 6).toNat < 2^48 := by
    have h := ha.2.2
    change ((a 6).toNat : ℤ) < 2^48 at h
    exact_mod_cast h
  have hall (i : Fin 7) : (a i).setWidth 56 = BitVec.allOnes 56 ↔
      unsigned (a i) = 2^56 - 1 := by
    rw [BitVec.toNat_eq, BitVec.toNat_allOnes, hlow]
    unfold unsigned
    norm_num
    exact_mod_cast Iff.rfl
  have h6 : (a 6).setWidth 56 ||| (71776119061217280 : BitVec 56) = BitVec.allOnes 56 ↔
      unsigned (a 6) = 2^48 - 1 := by
    change (a 6).setWidth 56 ||| ~~~BitVec.ofNat 56 (2^48 - 1) = _ ↔ _
    rw [or_not_lowMask_ones _ 48 (by decide), hlow, Nat.mod_eq_of_lt htop]
    unfold unsigned
    norm_num
    exact_mod_cast Iff.rfl
  have h2h : (a 2).setWidth 56 ||| (131071 : BitVec 56) = BitVec.allOnes 56 ↔
      unsigned (a 2) / 2^17 = 2^39 - 1 := by
    rw [or_low17_ones, hlow]
    unfold unsigned
    norm_num
    exact_mod_cast Iff.rfl
  have h2b : (a 2).setWidth 56 ||| ~~~(65536 : BitVec 56) = BitVec.allOnes 56 ↔
      unsigned (a 2) / 2^16 % 2 = 1 := by
    rw [or_not_bit16_ones, hlow]
    unfold unsigned
    norm_num
    exact_mod_cast Iff.rfl
  have h2l : (a 2).setWidth 56 ||| (72057594037862400 : BitVec 56) = BitVec.allOnes 56 ↔
      unsigned (a 2) % 2^16 = 2^16 - 1 := by
    change (a 2).setWidth 56 ||| ~~~BitVec.ofNat 56 (2^16 - 1) = _ ↔ _
    rw [or_not_lowMask_ones _ 16 (by decide), hlow]
    unfold unsigned
    norm_num
    exact_mod_cast Iff.rfl
  have h1h : (a 1).setWidth 56 ||| (1099511627775 : BitVec 56) = BitVec.allOnes 56 ↔
      unsigned (a 1) / 2^40 = 2^16 - 1 := by
    rw [or_low40_ones, hlow]
    unfold unsigned
    norm_num
    exact_mod_cast Iff.rfl
  have h1l : (a 1).setWidth 56 &&& ~~~(72056494526300160 : BitVec 56) = 0 ↔
      unsigned (a 1) % 2^40 = 0 := by
    change (a 1).setWidth 56 &&& BitVec.ofNat 56 (2^40 - 1) = 0 ↔ _
    rw [BitVec.toNat_eq, lowMask_toNat _ 40 (by decide), hlow]
    change (a 1).toNat % 2^40 = 0 ↔ ((a 1).toNat : ℤ) % 2^40 = 0
    exact_mod_cast (Iff.rfl : (a 1).toNat % 2^40 = 0 ↔ (a 1).toNat % 2^40 = 0)
  have h0h : (a 0).setWidth 56 &&& ~~~(4294967295 : BitVec 56) = 0 ↔
      unsigned (a 0) / 2^32 = 0 := by
    change (a 0).setWidth 56 &&& ~~~BitVec.ofNat 56 (2^32 - 1) = 0 ↔ _
    rw [and_not_lowMask_zero _ 32 (by decide), hlow]
    change (a 0).toNat / 2^32 = 0 ↔ ((a 0).toNat : ℤ) / 2^32 = 0
    exact_mod_cast (Iff.rfl : (a 0).toNat / 2^32 = 0 ↔ (a 0).toNat / 2^32 = 0)
  have h0l : (a 0).setWidth 56 ||| (72057589742960640 : BitVec 56) = BitVec.allOnes 56 ↔
      unsigned (a 0) % 2^32 = 2^32 - 1 := by
    change (a 0).setWidth 56 ||| ~~~BitVec.ofNat 56 (2^32 - 1) = _ ↔ _
    rw [or_not_lowMask_ones _ 32 (by decide), hlow]
    unfold unsigned
    norm_num
    exact_mod_cast Iff.rfl
  have hcast0 : (71776119061217280 : BitVec 64).setWidth 56 = (71776119061217280 : BitVec 56) := by decide
  have hcast1 : (131071 : BitVec 64).setWidth 56 = (131071 : BitVec 56) := by decide
  have hcast2 : (65536 : BitVec 64).setWidth 56 = (65536 : BitVec 56) := by decide
  have hcast3 : (72057594037862400 : BitVec 64).setWidth 56 = (72057594037862400 : BitVec 56) := by decide
  have hcast4 : (1099511627775 : BitVec 64).setWidth 56 = (1099511627775 : BitVec 56) := by decide
  have hcast5 : (72056494526300160 : BitVec 64).setWidth 56 = (72056494526300160 : BitVec 56) := by decide
  have hcast6 : (4294967295 : BitVec 64).setWidth 56 = (4294967295 : BitVec 56) := by decide
  have hcast7 : (72057589742960640 : BitVec 64).setWidth 56 = (72057589742960640 : BitVec 56) := by decide
  have hp0 :
      (((((a 6 ||| (71776119061217280 : BitVec 64)) &&& a 5) &&& a 4) &&& a 3) &&&
        (a 2 ||| (131071 : BitVec 64))).setWidth 56 = BitVec.allOnes 56 ↔
        contractPredicates (fun j => unsigned (a j)) 0 := by
    simp only [BitVec.setWidth_and, BitVec.setWidth_or,
      BitVec.setWidth_ofNat_of_le (by decide : 56 ≤ 64), BitVec.and_eq_allOnes_iff,
      hcast0, hcast1, hcast2, hcast3, hcast4, hcast5, hcast6, hcast7, h6, h2h, hall]
    change _ ↔ (unsigned (a 6) = 2^48 - 1 ∧ unsigned (a 5) = 2^56 - 1 ∧
      unsigned (a 4) = 2^56 - 1 ∧ unsigned (a 3) = 2^56 - 1 ∧
      unsigned (a 2) / 2^17 = 2^39 - 1)
    tauto
  have hp1 : (a 2 ||| ~~~(65536 : BitVec 64)).setWidth 56 = BitVec.allOnes 56 ↔
      contractPredicates (fun j => unsigned (a j)) 1 := by
    simpa only [BitVec.setWidth_or, BitVec.setWidth_not (by decide : 56 ≤ 64),
      BitVec.setWidth_ofNat_of_le (by decide : 56 ≤ 64)] using h2b
  have hp2 : ((a 2 ||| (72057594037862400 : BitVec 64)) &&&
      (a 1 ||| (1099511627775 : BitVec 64))).setWidth 56 = BitVec.allOnes 56 ↔
      contractPredicates (fun j => unsigned (a j)) 2 := by
    simp only [BitVec.setWidth_and, BitVec.setWidth_or,
      BitVec.setWidth_ofNat_of_le (by decide : 56 ≤ 64), BitVec.and_eq_allOnes_iff,
      hcast3, hcast4, h2l, h1h]
    rfl
  have hp3 : ((a 1 &&& ~~~(72056494526300160 : BitVec 64)) |||
      (a 0 &&& ~~~(4294967295 : BitVec 64))).setWidth 56 = 0 ↔
      contractPredicates (fun j => unsigned (a j)) 3 := by
    have ho (x y : BitVec 56) : x ||| y = (0 : BitVec 56) ↔
        x = (0 : BitVec 56) ∧ y = (0 : BitVec 56) := BitVec.or_eq_zero_iff
    simp only [BitVec.setWidth_and, BitVec.setWidth_or,
      BitVec.setWidth_not (by decide : 56 ≤ 64),
      BitVec.setWidth_ofNat_of_le (by decide : 56 ≤ 64),
      hcast5, hcast6, ho, h1l, h0h]
    rfl
  have hp4 : (a 0 ||| (72057589742960640 : BitVec 64)).setWidth 56 = BitVec.allOnes 56 ↔
      contractPredicates (fun j => unsigned (a j)) 4 := by
    simpa only [BitVec.setWidth_or, BitVec.setWidth_ofNat_of_le (by decide : 56 ≤ 64)] using h0l
  let raw0 := ((((a 6 ||| (71776119061217280 : BitVec 64)) &&& a 5) &&& a 4) &&& a 3) &&&
    (a 2 ||| (131071 : BitVec 64))
  let raw1 := a 2 ||| ~~~(65536 : BitVec 64)
  let raw2 := (a 2 ||| (72057594037862400 : BitVec 64)) &&& (a 1 ||| (1099511627775 : BitVec 64))
  let raw3 := (a 1 &&& ~~~(72056494526300160 : BitVec 64)) ||| (a 0 &&& ~~~(4294967295 : BitVec 64))
  let raw4 := a 0 ||| (72057589742960640 : BitVec 64)
  have hc0 : (machineContractConditionsTrace a).conditions 0 =
      if contractPredicates (fun j => unsigned (a j)) 0 then BitVec.allOnes 64 else 0 := by
    change zeroMask ((raw0 + 1) &&& (72057594037927935 : BitVec 64)) = _
    rw [contractMask_succ]
    simp only [raw0, hp0]
  have hc1 : (machineContractConditionsTrace a).conditions 1 =
      if contractPredicates (fun j => unsigned (a j)) 1 then BitVec.allOnes 64 else 0 := by
    change zeroMask ((raw1 + 1) &&& (72057594037927935 : BitVec 64)) = _
    rw [contractMask_succ]
    simp only [raw1, hp1]
  have hc2 : (machineContractConditionsTrace a).conditions 2 =
      if contractPredicates (fun j => unsigned (a j)) 2 then BitVec.allOnes 64 else 0 := by
    change zeroMask ((raw2 + 1) &&& (72057594037927935 : BitVec 64)) = _
    rw [contractMask_succ]
    simp only [raw2, hp2]
  have hc3 : (machineContractConditionsTrace a).conditions 3 =
      if contractPredicates (fun j => unsigned (a j)) 3 then BitVec.allOnes 64 else 0 := by
    change zeroMask (raw3 &&& (72057594037927935 : BitVec 64)) = _
    rw [contractMask_correct]
    simp only [raw3, hp3]
  have hc4 : (machineContractConditionsTrace a).conditions 4 =
      if contractPredicates (fun j => unsigned (a j)) 4 then BitVec.allOnes 64 else 0 := by
    change zeroMask ((raw4 + 1) &&& (72057594037927935 : BitVec 64)) = _
    rw [contractMask_succ]
    simp only [raw4, hp4]
  funext i
  fin_cases i
  exact hc0
  exact hc1
  exact hc2
  exact hc3
  exact hc4

end P384
