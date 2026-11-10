import P384.Booth
import P384.Comb

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192

namespace P384

def packScalar6 (a b c d e f : Byte) : BitVec 64 :=
  ((a.setWidth 32 <<< 5).setWidth 64) |||
  ((b.setWidth 32 <<< 4).setWidth 64) |||
  ((c.setWidth 32 <<< 3).setWidth 64) |||
  ((d.setWidth 32 <<< 2).setWidth 64) |||
  ((e.setWidth 32 <<< 1).setWidth 64) ||| f.setWidth 64

theorem packScalar6_bits (a b c d e f : BitVec 1) :
    (packScalar6 (a.setWidth 8) (b.setWidth 8) (c.setWidth 8)
      (d.setWidth 8) (e.setWidth 8) (f.setWidth 8)).toNat =
      32 * a.toNat + 16 * b.toNat + 8 * c.toNat + 4 * d.toNat + 2 * e.toNat + f.toNat := by
  revert a b c d e f
  decide

theorem bitByte_roundtrip (b : Byte) (h : b.toNat < 2) : (b.setWidth 1).setWidth 8 = b := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth]
  rw [Nat.mod_eq_of_lt h, Nat.mod_eq_of_lt b.isLt]

theorem packScalar6_correct (a b c d e f : Byte)
    (ha : a.toNat < 2) (hb : b.toNat < 2) (hc : c.toNat < 2)
    (hd : d.toNat < 2) (he : e.toNat < 2) (hf : f.toNat < 2) :
    (packScalar6 a b c d e f).toNat =
      32 * a.toNat + 16 * b.toNat + 8 * c.toNat + 4 * d.toNat + 2 * e.toNat + f.toNat := by
  have h := packScalar6_bits (a.setWidth 1) (b.setWidth 1) (c.setWidth 1)
    (d.setWidth 1) (e.setWidth 1) (f.setWidth 1)
  simpa only [bitByte_roundtrip a ha, bitByte_roundtrip b hb, bitByte_roundtrip c hc,
    bitByte_roundtrip d hd, bitByte_roundtrip e he, bitByte_roundtrip f hf,
    BitVec.toNat_setWidth, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb, Nat.mod_eq_of_lt hc,
    Nat.mod_eq_of_lt hd, Nat.mod_eq_of_lt he, Nat.mod_eq_of_lt hf] using h

def machineBoothWindow (bs : List Byte) (i : ℕ) : BitVec 64 :=
  packScalar6 (machineGetBit bs (i + 4 : ℕ)) (machineGetBit bs (i + 3 : ℕ))
    (machineGetBit bs (i + 2 : ℕ)) (machineGetBit bs (i + 1 : ℕ))
    (machineGetBit bs i) (machineGetBit bs ((i : ℤ) - 1))

theorem machineBoothWindow_correct (bs : List Byte) (hl : bs.length = 48) (i : ℕ) :
    (machineBoothWindow bs i).toNat = boothBitWindow (leValue bs) i := by
  have hb (j : ℤ) : (machineGetBit bs j).toNat < 2 := by
    rw [machineGetBit_correct bs hl]
    exact scalarBit_bound _ _
  rw [machineBoothWindow, packScalar6_correct _ _ _ _ _ _ (hb _) (hb _) (hb _) (hb _) (hb _) (hb _)]
  simp only [machineGetBit_correct bs hl, boothBitWindow]

theorem machineBoothWindow_recode (bs : List Byte) (hl : bs.length = 48) (j : ℕ) :
    let result := machineBoothRecode ((machineBoothWindow bs (5 * j)).setWidth 8)
    result.1.toNat ≤ 1 ∧ result.2.toNat ≤ 16 ∧
      signedDigit result.1 result.2 = boothValue (boothWindow (leValue bs) j) := by
  have hv := machineBoothWindow_correct bs hl (5 * j)
  rw [boothBitWindow_eq] at hv
  have hbound : (machineBoothWindow bs (5 * j)).toNat < 64 := by
    rw [hv]
    exact boothWindow_bound _ _
  have hn : ((machineBoothWindow bs (5 * j)).setWidth 8).toNat = boothWindow (leValue bs) j := by
    rw [BitVec.toNat_setWidth, hv, Nat.mod_eq_of_lt ((boothWindow_bound _ _).trans (by decide))]
  have h := machineBoothRecode_correct_byte ((machineBoothWindow bs (5 * j)).setWidth 8) (by omega)
  simpa only [hn] using h

def packScalar4 (a b c d : Byte) : BitVec 64 :=
  ((a.setWidth 32 <<< 3).setWidth 64) ||| ((b.setWidth 32 <<< 2).setWidth 64) |||
    ((c.setWidth 32 <<< 1).setWidth 64) ||| d.setWidth 64

theorem packScalar4_bits (a b c d : BitVec 1) :
    (packScalar4 (a.setWidth 8) (b.setWidth 8) (c.setWidth 8) (d.setWidth 8)).toNat =
      8 * a.toNat + 4 * b.toNat + 2 * c.toNat + d.toNat := by
  revert a b c d
  decide

theorem packScalar4_correct (a b c d : Byte)
    (ha : a.toNat < 2) (hb : b.toNat < 2) (hc : c.toNat < 2) (hd : d.toNat < 2) :
    (packScalar4 a b c d).toNat = 8 * a.toNat + 4 * b.toNat + 2 * c.toNat + d.toNat := by
  have h := packScalar4_bits (a.setWidth 1) (b.setWidth 1) (c.setWidth 1) (d.setWidth 1)
  simpa only [bitByte_roundtrip a ha, bitByte_roundtrip b hb, bitByte_roundtrip c hc,
    bitByte_roundtrip d hd, BitVec.toNat_setWidth, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb,
    Nat.mod_eq_of_lt hc, Nat.mod_eq_of_lt hd] using h

def machineCombWindow (bs : List Byte) (i : ℕ) : BitVec 64 :=
  packScalar4 (machineGetBit bs (i + 285 : ℕ))
    (if i < 95 then machineGetBit bs (i + 190 : ℕ) else 0)
    (if i < 95 then machineGetBit bs (i + 95 : ℕ) else 0)
    (if i < 95 then machineGetBit bs i else 0)

theorem machineCombWindow_correct (bs : List Byte) (hl : bs.length = 48) (i : ℕ) :
    (machineCombWindow bs i).toNat = combIndex (leValue bs) i := by
  have hb (j : ℤ) : (machineGetBit bs j).toNat < 2 := by
    rw [machineGetBit_correct bs hl]
    exact scalarBit_bound _ _
  by_cases hi : i < 95
  · simp only [machineCombWindow, if_pos hi]
    rw [packScalar4_correct _ _ _ _ (hb _) (hb _) (hb _) (hb _)]
    simp only [machineGetBit_correct bs hl, combIndex, if_pos hi]
    omega
  · simp only [machineCombWindow, if_neg hi]
    rw [packScalar4_correct _ _ _ _ (hb _) (by decide) (by decide) (by decide)]
    simp [machineGetBit_correct bs hl, combIndex, hi]

end P384
