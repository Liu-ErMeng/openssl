import P384.BNLength

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option exponentiation.threshold 2048

namespace P384

structure BNToFelemResult where
  status : ℤ
  limbs : Fin 7 → BitVec 64
  scratch : ByteMemory

def bnToFelemCall (s : BN64State) (out : Fin 7 → BitVec 64) (mem : ByteMemory) (off : ℕ) : BNToFelemResult :=
  if s.negative then ⟨0, out, mem⟩ else
  let padded := bnPadExportCall s mem off 48
  if padded.status < 0 then ⟨0, out, padded.memory⟩
  else ⟨1, bin48ToFelem (readMemory padded.memory off 48), padded.memory⟩

theorem bnToFelemCall_eq (s : BN64State) (out : Fin 7 → BitVec 64) (mem : ByteMemory) (off : ℕ) :
    bnToFelemCall s out mem off =
      if s.negative then ⟨0, out, mem⟩ else
      if bnPadLengthAccept s 48 then
        let padded := writeMemory mem off (bnExportLE (bnWordBytes s.words) (8 * s.top) 48)
        ⟨1, bin48ToFelem (readMemory padded off 48), padded⟩
      else ⟨0, out, mem⟩ := by
  simp only [bnToFelemCall, bnPadExportCall48_eq]
  cases s.negative <;> cases bnPadLengthAccept s 48 <;> rfl

theorem bnToFelemCall_success (s : BN64State) (hs : BN64Valid s)
    (out : Fin 7 → BitVec 64) (mem : ByteMemory) (off : ℕ) :
    (bnToFelemCall s out mem off).status = 1 ↔ s.negative = false ∧ bnMagnitude s < 2^384 := by
  have he := bnPadLengthAccept48_correct s hs
  rw [bnToFelemCall_eq]
  cases hn : s.negative <;> cases hb : bnPadLengthAccept s 48 <;> simp_all

theorem bnToFelemCall_failure_frame (s : BN64State) (hs : BN64Valid s)
    (out : Fin 7 → BitVec 64) (mem : ByteMemory) (off : ℕ)
    (hf : s.negative = true ∨ 2^384 ≤ bnMagnitude s) :
    (bnToFelemCall s out mem off).status = 0 ∧
      (bnToFelemCall s out mem off).limbs = out ∧ (bnToFelemCall s out mem off).scratch = mem := by
  have he := bnPadLengthAccept48_correct s hs
  rw [bnToFelemCall_eq]
  cases hn : s.negative <;> cases hb : bnPadLengthAccept s 48 <;> simp_all
  omega

theorem bnToFelemCall_value (s : BN64State) (hs : BN64Valid s)
    (out : Fin 7 → BitVec 64) (mem : ByteMemory) (off : ℕ)
    (hn : s.negative = false) (hv : bnMagnitude s < 2^384) :
    eval7 (fun i => unsigned ((bnToFelemCall s out mem off).limbs i)) = bnMagnitude s ∧
      serialFelem (fun i => unsigned ((bnToFelemCall s out mem off).limbs i)) := by
  have hb := bnPadExportCall48_bytes s hs mem off hv
  have he := (bnPadLengthAccept48_correct s hs).2 hv
  rw [bnPadExportCall48_eq] at hb
  simp only [he, ↓reduceIte] at hb
  rw [bnToFelemCall_eq]
  simp only [hn, Bool.false_eq_true, ↓reduceIte, he, hb]
  constructor
  · rw [bin48ToFelem_value _ (by simp), leValue_encodeLE]
    exact_mod_cast Nat.mod_eq_of_lt hv
  · exact bin48ToFelem_serial _

theorem bnToFelemCall_checked (s : BN64State) (hs : BN64Valid s)
    (out : Fin 7 → BitVec 64) (mem : ByteMemory) (off : ℕ)
    (hret : (bnToFelemCall s out mem off).status = 1) :
    eval7 (fun i => unsigned ((bnToFelemCall s out mem off).limbs i)) = bnMagnitude s ∧
      serialFelem (fun i => unsigned ((bnToFelemCall s out mem off).limbs i)) := by
  obtain ⟨hn, hv⟩ := (bnToFelemCall_success s hs out mem off).1 hret
  exact bnToFelemCall_value s hs out mem off hn hv

end P384
