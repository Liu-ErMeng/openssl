import P384.BNBytes
import P384.Serialization

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option exponentiation.threshold 1024

namespace P384

def bnLoadByte (allocated : List Byte) (i : ℕ) : Byte :=
  (load64LE (allocated.drop (8 * (i / 8))) >>> (8 * (i % 8))).setWidth 8

theorem bnLoadByte_correct (allocated : List Byte) (i : ℕ) :
    bnLoadByte allocated i = allocated.getD i 0 := by
  have hp : (2 : ℕ)^(8 * (i % 8)) = 256^(i % 8) := by rw [pow_mul]; rfl
  have hbyte : bnLoadByte allocated i =
      byteAt (leValue ((allocated.drop (8 * (i / 8))).take 8)) (i % 8) := by
    apply BitVec.eq_of_toNat_eq
    simp only [bnLoadByte, BitVec.toNat_setWidth, BitVec.toNat_ushiftRight,
      Nat.shiftRight_eq_div_pow, load64LE_value, hp, byteAt, BitVec.toNat_ofNat]
  rw [hbyte, byteAt_leValue]
  simp only [List.getD_eq_getElem?_getD, List.getElem?_take,
    Nat.mod_lt i (by decide : 0 < 8), ↓reduceIte, List.getElem?_drop]
  rw [Nat.div_add_mod i 8]

def bnExportByte (allocated : List Byte) (topBytes j : ℕ) : Byte :=
  if allocated.length = 0 then 0 else
  let i := (bnExportCursor (BitVec.ofNat 64 (allocated.length - 1)) j).toNat
  let l := load64LE (allocated.drop (8 * (i / 8)))
  ((l >>> (8 * (i % 8))) &&&
    bnExportMask (BitVec.ofNat 64 j) (BitVec.ofNat 64 topBytes)).setWidth 8

theorem bnExportByte_correct (allocated : List Byte) (topBytes j : ℕ)
    (ht : topBytes ≤ allocated.length) (hc : allocated.length < 2^63)
    (hj : j < 2^63) :
    bnExportByte allocated topBytes j = (allocated.take topBytes).getD j 0 := by
  by_cases hz : allocated.length = 0
  · have he : allocated = [] := List.eq_nil_of_length_eq_zero hz
    subst allocated
    simp [bnExportByte]
  · have hn : (BitVec.ofNat 64 (allocated.length - 1)).toNat = allocated.length - 1 := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    have hcurs := bnExportCursor_correct (BitVec.ofNat 64 (allocated.length - 1))
      (by rw [hn]; omega) j
    rw [hn] at hcurs
    have hjn : (BitVec.ofNat 64 j).toNat = j := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    have htn : (BitVec.ofNat 64 topBytes).toNat = topBytes := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    have hmask := bnExportMask_correct (BitVec.ofNat 64 j) (BitVec.ofNat 64 topBytes)
      (by rw [hjn]; exact hj) (by rw [htn]; omega)
    rw [hjn, htn] at hmask
    simp only [bnExportByte, hz, ↓reduceIte, hcurs, hmask]
    by_cases hjt : j < topBytes
    · rw [if_pos hjt, Nat.min_eq_left (by omega), BitVec.and_allOnes]
      change bnLoadByte allocated j = _
      rw [bnLoadByte_correct]
      simp only [List.getD_eq_getElem?_getD, List.getElem?_take, hjt, ↓reduceIte]
    · rw [if_neg hjt]
      simp [List.getD_eq_getElem?_getD, List.getElem?_take, hjt]

def bnExportLE (allocated : List Byte) (topBytes n : ℕ) : List Byte :=
  (List.range n).map (bnExportByte allocated topBytes)

theorem bnExportLE_correct (allocated : List Byte) (topBytes n : ℕ)
    (ht : topBytes ≤ allocated.length) (hc : allocated.length < 2^63)
    (hn : n ≤ 2^63) :
    bnExportLE allocated topBytes n = encodeLE n (leValue (allocated.take topBytes)) := by
  apply List.ext_getElem
  · simp [bnExportLE]
  · intro i hi hi'
    have hi : i < n := by simpa [bnExportLE] using hi
    simp only [bnExportLE, List.getElem_map, List.getElem_range,
      encodeLE_get n _ i hi]
    rw [bnExportByte_correct allocated topBytes i ht hc (by omega), byteAt_leValue]

theorem bnExportLE_value (allocated : List Byte) (topBytes n : ℕ)
    (ht : topBytes ≤ allocated.length) (hc : allocated.length < 2^63)
    (hn : n ≤ 2^63) :
    leValue (bnExportLE allocated topBytes n) = leValue (allocated.take topBytes) % 256^n := by
  rw [bnExportLE_correct allocated topBytes n ht hc hn, leValue_encodeLE]

theorem bnExportLE48_to_felem (allocated : List Byte) (topBytes : ℕ)
    (ht : topBytes ≤ allocated.length) (hc : allocated.length < 2^63)
    (hv : leValue (allocated.take topBytes) < 2^384) :
    eval7 (fun i => unsigned (bin48ToFelem (bnExportLE allocated topBytes 48) i)) =
      leValue (allocated.take topBytes) := by
  rw [bin48ToFelem_value _ (by simp [bnExportLE]),
    bnExportLE_value allocated topBytes 48 ht hc (by norm_num)]
  change ((leValue (allocated.take topBytes) % 2^384 : ℕ) : ℤ) = _
  rw [Nat.mod_eq_of_lt hv]

end P384
