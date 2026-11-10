import P384.ByteMemory

set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace P384

def serializeStores : ℕ → ByteMemory → ℕ → (Fin 7 → BitVec 64) → ByteMemory
  | 0, mem, _, _ => mem
  | n + 1, mem, off, a =>
      orStoreWord (serializeStores n mem off a) (off + 7 * n)
        (a ⟨n % 7, Nat.mod_lt _ (by decide)⟩ &&& BitVec.ofNat 64 (2^56 - 1))

def serializedPrefix : ℕ → (Fin 7 → BitVec 64) → List Byte
  | 0, _ => []
  | n + 1, a => serializedPrefix n a ++
      encodeLE 7 (a ⟨n % 7, Nat.mod_lt _ (by decide)⟩).toNat

@[simp] theorem serializedPrefix_length (n : ℕ) (a : Fin 7 → BitVec 64) :
    (serializedPrefix n a).length = 7 * n := by
  induction n <;> simp [serializedPrefix, *, Nat.mul_add]

theorem serializeStores_correct (n : ℕ) (mem : ByteMemory) (off : ℕ)
    (a : Fin 7 → BitVec 64) (hz : ∀ k < 7 * n, mem (off + k) = 0) :
    serializeStores n mem off a = writeMemory mem off (serializedPrefix n a) := by
  induction n with
  | zero =>
      funext j
      simp only [serializeStores, serializedPrefix, writeMemory, List.length_nil, Nat.add_zero]
      rw [if_neg (show ¬(off ≤ j ∧ j < off) by omega)]
  | succ n ih =>
      rw [serializeStores, ih (by intro k hk; apply hz; omega)]
      rw [orStoreWord_mask56]
      · simpa only [serializedPrefix, serializedPrefix_length] using
          writeMemory_append mem off (serializedPrefix n a)
            (encodeLE 7 (a ⟨n % 7, Nat.mod_lt _ (by decide)⟩).toNat)
      · intro k hk
        rw [writeMemory_frame _ _ _ _ (Or.inr (by simp only [serializedPrefix_length]; omega))]
        simpa only [Nat.add_assoc] using hz (7 * n + k) (by omega)

def serializeMemory (mem : ByteMemory) (off : ℕ) (a : Fin 7 → BitVec 64) : ByteMemory :=
  let cleared := writeMemory mem off (List.replicate 48 0)
  let stored := serializeStores 6 cleared off a
  writeMemory stored (off + 42) (encodeLE 6 (a 6).toNat)

theorem serializeMemory_correct (mem : ByteMemory) (off : ℕ) (a : Fin 7 → BitVec 64) :
    serializeMemory mem off a = writeMemory mem off (felemBytes (fun i => unsigned (a i))) := by
  have hz : ∀ k < 42, writeMemory mem off (List.replicate 48 0) (off + k) = 0 := by
    intro k hk
    rw [writeMemory_at _ _ _ k (by simp only [List.length_replicate]; omega)]
    simp only [List.getD_eq_getElem?_getD, List.getElem?_replicate,
      show k < 48 by omega, ↓reduceIte, Option.getD_some]
  unfold serializeMemory
  dsimp only
  rw [serializeStores_correct 6 _ off a hz]
  have hlen : (serializedPrefix 6 a).length = 42 := by simp
  rw [← hlen, writeMemory_append]
  have he : serializedPrefix 6 a ++ encodeLE 6 (a 6).toNat =
      felemBytes (fun i => unsigned (a i)) := by
    simp only [serializedPrefix, felemBytes, unsigned, Int.toNat_natCast]
    rfl
  rw [he, writeMemory_overwrite _ _ _ _ (by simp)]

theorem serializeMemory_frame (mem : ByteMemory) (off : ℕ) (a : Fin 7 → BitVec 64) (j : ℕ)
    (hj : j < off ∨ off + 48 ≤ j) : serializeMemory mem off a j = mem j := by
  rw [serializeMemory_correct]
  exact writeMemory_frame mem off _ j (by simpa using hj)

theorem serializeMemory_value (mem : ByteMemory) (off : ℕ) (a : Fin 7 → BitVec 64)
    (ha : serialFelem (fun i => unsigned (a i))) :
    (leValue (readMemory (serializeMemory mem off a) off 48) : ℤ) =
      eval7 (fun i => unsigned (a i)) := by
  rw [serializeMemory_correct]
  have he := read_writeMemory mem off (felemBytes (fun i => unsigned (a i)))
  rw [felemBytes_length] at he
  rw [he, felemBytes_value _ ha]

theorem serialization_word_bounds (off : ℕ) (i : Fin 6) :
    off ≤ off + 7 * i.val ∧ off + 7 * i.val + 8 ≤ off + 48 := by omega

theorem serialization_tail_bounds (off : ℕ) : off + 42 + 6 = off + 48 := by omega

end P384
