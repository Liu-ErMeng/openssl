import P384.Words

set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace P384

abbrev PointWords := Fin 21 → BitVec 64

def selectRow (table : ℕ → PointWords) (idx i : ℕ) (out : PointWords) : PointWords :=
  fun j => out j ||| (table i j &&& selectionMask (BitVec.ofNat 64 i) (BitVec.ofNat 64 idx))

def selectLoop (table : ℕ → PointWords) (idx : ℕ) : ℕ → PointWords
  | 0 => fun _ => 0
  | k + 1 => selectRow table idx k (selectLoop table idx k)

theorem selectionMask_nat (i idx : ℕ) (hi : i < 32) (hx : idx < 32) :
    selectionMask (BitVec.ofNat 64 i) (BitVec.ofNat 64 idx) =
      if i = idx then BitVec.allOnes 64 else 0 := by
  have h := selectionMask_correct (BitVec.ofNat 5 i) (BitVec.ofNat 5 idx)
  have he (n : ℕ) (hn : n < 32) : (BitVec.ofNat 5 n).zeroExtend 64 = BitVec.ofNat 64 n := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.zeroExtend_eq_setWidth, BitVec.toNat_setWidth, BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt hn]
  have hx' : (BitVec.ofNat 5 i = BitVec.ofNat 5 idx) ↔ i = idx := by
    constructor
    · intro h
      have ht := congrArg BitVec.toNat h
      simpa only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hi, Nat.mod_eq_of_lt hx] using ht
    · exact congrArg _
  simpa only [he i hi, he idx hx, hx'] using h

theorem selectLoop_correct (table : ℕ → PointWords) (idx k : ℕ)
    (hx : idx < 32) (hk : k ≤ 32) :
    selectLoop table idx k = if idx < k then table idx else fun _ => 0 := by
  induction k with
  | zero => simp [selectLoop]
  | succ k ih =>
      rw [selectLoop, ih (by omega)]
      unfold selectRow
      rw [selectionMask_nat k idx (by omega) hx]
      by_cases he : k = idx
      · subst idx
        funext j
        simp only [if_pos rfl, Nat.lt_irrefl, if_false, BitVec.zero_or,
          Nat.lt_succ_self, if_true, BitVec.and_allOnes]
        exact BitVec.zero_or
      · rw [if_neg he]
        by_cases hl : idx < k
        · simp [hl, show idx < k + 1 by omega]
        · simp [hl, show ¬idx < k + 1 by omega]

theorem selectPoint17_correct (table : ℕ → PointWords) (idx : ℕ) (hx : idx < 17) :
    selectLoop table idx 17 = table idx := by
  rw [selectLoop_correct table idx 17 (by omega) (by decide), if_pos hx]

theorem selectPoint16_correct (table : ℕ → PointWords) (idx : ℕ) (hx : idx < 16) :
    selectLoop table idx 16 = table idx := by
  rw [selectLoop_correct table idx 16 (by omega) (by decide), if_pos hx]

theorem selectLoop_read_bounds (size i : ℕ) (hi : i < size) (j : Fin 21) :
    i * 21 + j.val < size * 21 := by omega

end P384
