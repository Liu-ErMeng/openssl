import P384.BNNumBits
import P384.InterfaceValues

set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option exponentiation.threshold 2048

namespace P384

def machineBNNumBytes (s : BN64State) : BitVec 32 :=
  (machineBNNumBits s + (7 : BitVec 32)).sdiv (8 : BitVec 32)

theorem machineBNNumBytes_correct (s : BN64State) (hs : BN64Valid s) :
    (machineBNNumBytes s).toNat = ((machineBNNumBits s).toNat + 7) / 8 := by
  have hb := (machineBNNumBits_signed s hs).2
  have ha : (machineBNNumBits s + (7 : BitVec 32)).toNat = (machineBNNumBits s).toNat + 7 := by
    rw [BitVec.toNat_add]
    change ((machineBNNumBits s).toNat + 7) % 2^32 = _
    rw [Nat.mod_eq_of_lt (by omega)]
  have hm : (machineBNNumBits s + (7 : BitVec 32)).msb = false := by
    apply BitVec.msb_eq_false_iff_two_mul_lt.2
    rw [ha]
    omega
  have h8 : (8 : BitVec 32).msb = false := by decide
  rw [machineBNNumBytes, BitVec.sdiv_eq, hm, h8]
  simp only [BitVec.udiv_eq, BitVec.toNat_udiv, ha, show (8 : BitVec 32).toNat = 8 from rfl]

theorem machineBNNumBytes_upper (s : BN64State) (hs : BN64Valid s) :
    ((bnMagnitude s).size + 7) / 8 ≤ (machineBNNumBytes s).toNat := by
  have hb := machineBNNumBits_upper s hs
  rw [machineBNNumBytes_correct s hs]
  omega

theorem machineBNNumBytes_normalized (s : BN64State) (hs : BN64Valid s) :
    (machineBNNumBytes (bnCorrectTop s)).toNat = ((bnMagnitude s).size + 7) / 8 := by
  rw [machineBNNumBytes_correct _ (bnCorrectTop_valid s hs), machineBNNumBits_normalized s hs]

def bnPadLengthAccept (s : BN64State) (tolen : ℕ) : Bool :=
  if tolen < (machineBNNumBytes s).toNat then
    decide (¬tolen < (machineBNNumBytes (bnCorrectTop s)).toNat)
  else true

theorem bnPadLengthAccept_correct (s : BN64State) (hs : BN64Valid s) (tolen : ℕ) :
    bnPadLengthAccept s tolen = true ↔ bnMagnitude s < 2^(8 * tolen) := by
  have hu := machineBNNumBytes_upper s hs
  have he := machineBNNumBytes_normalized s hs
  have hn : bnPadLengthAccept s tolen = true ↔ (bnMagnitude s).size ≤ 8 * tolen := by
    unfold bnPadLengthAccept
    by_cases hb : tolen < (machineBNNumBytes s).toNat
    · rw [if_pos hb, he]
      simp only [decide_eq_true_eq]
      omega
    · rw [if_neg hb]
      constructor
      · intro _
        omega
      · intro _
        rfl
  exact hn.trans Nat.size_le

theorem bnPadLengthAccept48_correct (s : BN64State) (hs : BN64Valid s) :
    bnPadLengthAccept s 48 = true ↔ bnMagnitude s < 2^384 := by
  exact bnPadLengthAccept_correct s hs 48

structure BNPadResult where
  status : ℤ
  memory : ByteMemory

def bnPadExportCall (s : BN64State) (mem : ByteMemory) (off : ℕ) (tolen : ℤ) : BNPadResult :=
  if tolen < 0 then ⟨-1, mem⟩ else
  if bnPadLengthAccept s tolen.toNat then
    ⟨tolen, writeMemory mem off (bnExportLE (bnWordBytes s.words) (8 * s.top) tolen.toNat)⟩
  else ⟨-1, mem⟩

theorem bnPadExportCall48_eq (s : BN64State) (mem : ByteMemory) (off : ℕ) :
    bnPadExportCall s mem off 48 =
      if bnPadLengthAccept s 48 then
        ⟨48, writeMemory mem off (bnExportLE (bnWordBytes s.words) (8 * s.top) 48)⟩
      else ⟨-1, mem⟩ := by rfl

theorem bnPadExportCall48_success (s : BN64State) (hs : BN64Valid s) (mem : ByteMemory) (off : ℕ) :
    (bnPadExportCall s mem off 48).status = 48 ↔ bnMagnitude s < 2^384 := by
  have he := bnPadLengthAccept48_correct s hs
  rw [bnPadExportCall48_eq]
  cases hb : bnPadLengthAccept s 48 <;> simp_all

theorem bnPadExportCall48_failure_frame (s : BN64State) (hs : BN64Valid s)
    (mem : ByteMemory) (off : ℕ) (hv : 2^384 ≤ bnMagnitude s) :
    (bnPadExportCall s mem off 48).status = -1 ∧ (bnPadExportCall s mem off 48).memory = mem := by
  have he : bnPadLengthAccept s 48 = false := by
    cases hh : bnPadLengthAccept s 48
    · rfl
    · have hc := (bnPadLengthAccept48_correct s hs).1 hh
      omega
  simp [bnPadExportCall, he]

theorem bnPadExportCall48_bytes (s : BN64State) (hs : BN64Valid s)
    (mem : ByteMemory) (off : ℕ) (hv : bnMagnitude s < 2^384) :
    readMemory (bnPadExportCall s mem off 48).memory off 48 = encodeLE 48 (bnMagnitude s) := by
  have he := (bnPadLengthAccept48_correct s hs).2 hv
  have hb := bnExportLE_correct (bnWordBytes s.words) (8 * s.top) 48
    (by have ht := hs.1; simp; omega) (by have hc := hs.2; simp; omega) (by norm_num)
  rw [bnWordBytes_take, bnWordBytes_value] at hb
  have hl : (bnExportLE (bnWordBytes s.words) (8 * s.top) 48).length = 48 := by simp [bnExportLE]
  have hr := read_writeMemory mem off (bnExportLE (bnWordBytes s.words) (8 * s.top) 48)
  rw [hl] at hr
  simpa only [bnPadExportCall48_eq, he, ↓reduceIte, bnMagnitude] using hr.trans hb

theorem bnPadExportCall48_value (s : BN64State) (hs : BN64Valid s)
    (mem : ByteMemory) (off : ℕ) (hv : bnMagnitude s < 2^384) :
    leValue (readMemory (bnPadExportCall s mem off 48).memory off 48) = bnMagnitude s := by
  rw [bnPadExportCall48_bytes s hs mem off hv, leValue_encodeLE]
  exact Nat.mod_eq_of_lt hv

theorem bnPadExportCall48_frame (s : BN64State) (mem : ByteMemory) (off j : ℕ)
    (hj : j < off ∨ off + 48 ≤ j) : (bnPadExportCall s mem off 48).memory j = mem j := by
  rw [bnPadExportCall48_eq]
  cases hb : bnPadLengthAccept s 48
  · rfl
  · exact writeMemory_frame mem off (bnExportLE (bnWordBytes s.words) (8 * s.top) 48) j
      (by simpa [bnExportLE] using hj)

end P384
