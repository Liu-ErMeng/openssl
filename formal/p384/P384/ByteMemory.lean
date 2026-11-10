import P384.Serialization

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace P384

abbrev ByteMemory := ℕ → Byte

def readMemory (mem : ByteMemory) (off n : ℕ) : List Byte :=
  List.ofFn (fun i : Fin n => mem (off + i.val))

@[simp] theorem readMemory_length (mem : ByteMemory) (off n : ℕ) :
    (readMemory mem off n).length = n := by simp [readMemory]

theorem readMemory_get (mem : ByteMemory) (off n k : ℕ) (hk : k < n) :
    (readMemory mem off n).getD k 0 = mem (off + k) := by
  simp [readMemory, List.getD_eq_getElem?_getD, hk]

theorem readMemory_slice (mem : ByteMemory) (off capacity start n : ℕ)
    (h : start + n ≤ capacity) :
    ((readMemory mem off capacity).drop start).take n = readMemory mem (off + start) n := by
  apply List.ext_getElem
  · simp only [List.length_take, List.length_drop, readMemory_length]
    omega
  · intro i hi hi'
    simp only [List.getElem_take, List.getElem_drop, readMemory, List.getElem_ofFn]
    congr 1
    omega

def writeMemory (mem : ByteMemory) (off : ℕ) (bs : List Byte) : ByteMemory := fun j =>
  if off ≤ j ∧ j < off + bs.length then bs.getD (j - off) 0 else mem j

theorem writeMemory_at (mem : ByteMemory) (off : ℕ) (bs : List Byte) (k : ℕ)
    (hk : k < bs.length) :
    writeMemory mem off bs (off + k) = bs.getD k 0 := by
  rw [writeMemory, if_pos (show off ≤ off + k ∧ off + k < off + bs.length by omega)]
  simp only [Nat.add_sub_cancel_left]

theorem writeMemory_frame (mem : ByteMemory) (off : ℕ) (bs : List Byte) (j : ℕ)
    (hj : j < off ∨ off + bs.length ≤ j) : writeMemory mem off bs j = mem j := by
  rw [writeMemory, if_neg (show ¬(off ≤ j ∧ j < off + bs.length) by omega)]

theorem read_writeMemory (mem : ByteMemory) (off : ℕ) (bs : List Byte) :
    readMemory (writeMemory mem off bs) off bs.length = bs := by
  apply List.ext_getElem
  · simp
  · intro i hi hi'
    have hi : i < bs.length := by simpa using hi
    have he := writeMemory_at mem off bs i hi
    simpa only [readMemory, List.getElem_ofFn, List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem hi, Option.getD_some] using he

def wordByte (w : BitVec 64) (i : ℕ) : Byte := (w >>> (8 * i)).setWidth 8

theorem wordByte_value (w : BitVec 64) (i : ℕ) : wordByte w i = byteAt w.toNat i := by
  apply BitVec.eq_of_toNat_eq
  simp only [wordByte, BitVec.toNat_setWidth, BitVec.toNat_ushiftRight,
    Nat.shiftRight_eq_div_pow, byteAt, BitVec.toNat_ofNat]
  rw [pow_mul]
  rfl

theorem wordByte_or (x y : BitVec 64) (i : ℕ) :
    wordByte (x ||| y) i = wordByte x i ||| wordByte y i := by
  simp only [wordByte, BitVec.ushiftRight_or_distrib, BitVec.setWidth_or]

theorem wordByte_mask56 (w : BitVec 64) (i : Fin 8) :
    wordByte (w &&& BitVec.ofNat 64 (2^56 - 1)) i =
      if i.val < 7 then wordByte w i else 0 := by
  simp only [wordByte, BitVec.ushiftRight_and_distrib, BitVec.setWidth_and]
  have hm : ((BitVec.ofNat 64 (2^56 - 1) >>> (8 * i.val)).setWidth 8) =
      if i.val < 7 then BitVec.allOnes 8 else 0 := by
    fin_cases i <;> decide
  rw [hm]
  split
  · exact BitVec.and_allOnes
  · simp

def readWord (mem : ByteMemory) (off : ℕ) : BitVec 64 := load64LE (readMemory mem off 8)

theorem wordByte_readWord (mem : ByteMemory) (off i : ℕ) (hi : i < 8) :
    wordByte (readWord mem off) i = mem (off + i) := by
  rw [wordByte_value, readWord, load64LE_value, List.take_of_length_le (by simp),
    byteAt_leValue, readMemory_get mem off 8 i hi]

def storeWord (mem : ByteMemory) (off : ℕ) (w : BitVec 64) : ByteMemory :=
  writeMemory mem off (encodeLE 8 w.toNat)

theorem storeWord_at (mem : ByteMemory) (off i : ℕ) (w : BitVec 64) (hi : i < 8) :
    storeWord mem off w (off + i) = wordByte w i := by
  rw [storeWord, writeMemory_at _ _ _ i (by simpa using hi), encodeLE_getD 8 _ i hi,
    wordByte_value]

def orStoreWord (mem : ByteMemory) (off : ℕ) (w : BitVec 64) : ByteMemory :=
  storeWord mem off (readWord mem off ||| w)

theorem orStoreWord_bytewise (mem : ByteMemory) (off : ℕ) (w : BitVec 64) (j : ℕ) :
    orStoreWord mem off w j =
      if off ≤ j ∧ j < off + 8 then mem j ||| wordByte w (j - off) else mem j := by
  by_cases hj : off ≤ j ∧ j < off + 8
  · have he : j = off + (j - off) := by omega
    rw [if_pos hj]
    unfold orStoreWord
    rw [he, storeWord_at _ _ _ _ (by omega), wordByte_or,
      wordByte_readWord _ _ _ (by omega)]
    rw [← he]
  · rw [if_neg hj]
    exact writeMemory_frame mem off (encodeLE 8 _) j (by simp only [encodeLE_length]; omega)

def memmoveBytes (mem : ByteMemory) (dst src n : ℕ) : ByteMemory :=
  writeMemory mem dst (readMemory mem src n)

theorem memmoveBytes_snapshot (mem : ByteMemory) (dst src n : ℕ) :
    readMemory (memmoveBytes mem dst src n) dst n = readMemory mem src n := by
  have h := read_writeMemory mem dst (readMemory mem src n)
  simpa only [memmoveBytes, readMemory_length] using h

theorem memmoveBytes_frame (mem : ByteMemory) (dst src n j : ℕ)
    (hj : j < dst ∨ dst + n ≤ j) : memmoveBytes mem dst src n j = mem j :=
  writeMemory_frame mem dst (readMemory mem src n) j (by simpa using hj)

theorem orStoreWord_mask56 (mem : ByteMemory) (off : ℕ) (w : BitVec 64)
    (hz : ∀ k < 7, mem (off + k) = 0) :
    orStoreWord mem off (w &&& BitVec.ofNat 64 (2^56 - 1)) =
      writeMemory mem off (encodeLE 7 w.toNat) := by
  funext j
  rw [orStoreWord_bytewise, writeMemory, encodeLE_length]
  by_cases h8 : off ≤ j ∧ j < off + 8
  · rw [if_pos h8, wordByte_mask56 w ⟨j - off, by omega⟩]
    by_cases h7 : j - off < 7
    · rw [if_pos h7, if_pos (show off ≤ j ∧ j < off + 7 by omega)]
      change mem j ||| wordByte w (j - off) = _
      have hm : mem j = 0 := by
        have he : off + (j - off) = j := by omega
        simpa only [he] using hz (j - off) h7
      rw [encodeLE_getD 7 _ _ h7, ← wordByte_value]
      simpa only [hm] using (BitVec.zero_or (x := wordByte w (j - off)))
    · rw [if_neg h7, if_neg (show ¬(off ≤ j ∧ j < off + 7) by omega)]
      simp
  · rw [if_neg h8, if_neg (show ¬(off ≤ j ∧ j < off + 7) by omega)]

theorem writeMemory_append (mem : ByteMemory) (off : ℕ) (xs ys : List Byte) :
    writeMemory (writeMemory mem off xs) (off + xs.length) ys =
      writeMemory mem off (xs ++ ys) := by
  funext j
  simp only [writeMemory, List.length_append]
  by_cases hx : off ≤ j ∧ j < off + xs.length
  · rw [if_neg (show ¬(off + xs.length ≤ j ∧ j < off + xs.length + ys.length) by omega),
      if_pos hx, if_pos (show off ≤ j ∧ j < off + (xs.length + ys.length) by omega)]
    simp only [List.getD_eq_getElem?_getD,
      List.getElem?_append_left (show j - off < xs.length by omega)]
  · by_cases hy : off + xs.length ≤ j ∧ j < off + xs.length + ys.length
    · rw [if_pos hy, if_pos (show off ≤ j ∧ j < off + (xs.length + ys.length) by omega)]
      simp only [List.getD_eq_getElem?_getD,
        List.getElem?_append_right (show xs.length ≤ j - off by omega)]
      congr 2
      omega
    · rw [if_neg hy, if_neg hx,
        if_neg (show ¬(off ≤ j ∧ j < off + (xs.length + ys.length)) by omega)]

theorem writeMemory_overwrite (mem : ByteMemory) (off : ℕ) (xs ys : List Byte)
    (hl : xs.length = ys.length) :
    writeMemory (writeMemory mem off xs) off ys = writeMemory mem off ys := by
  funext j
  simp only [writeMemory, hl]
  split <;> simp_all

end P384
