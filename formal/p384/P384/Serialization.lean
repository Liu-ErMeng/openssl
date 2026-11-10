import P384.Bytes
import P384.Representation

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace P384

def load64LE (bs : List Byte) : BitVec 64 := BitVec.ofNat 64 (leValue (bs.take 8))

theorem load64LE_value (bs : List Byte) :
    (load64LE bs).toNat = leValue (bs.take 8) := by
  have h := leValue_bound (bs.take 8)
  have hp : 256^(bs.take 8).length ≤ 2^64 := by
    calc
      _ ≤ 256^8 := Nat.pow_le_pow_of_le (by decide) (List.length_take_le _ _)
      _ = _ := by norm_num
  exact Nat.mod_eq_of_lt (h.trans_le hp)

theorem load64LE_low56 (bs : List Byte) :
    (load64LE bs &&& BitVec.ofNat 64 (2^56 - 1)).toNat = leValue (bs.take 7) := by
  rw [BitVec.toNat_and, load64LE_value, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (show (2^56 - 1 : ℕ) < 2^64 by norm_num)]
  rw [Nat.and_two_pow_sub_one_eq_mod]
  rw [← show (256 : ℕ)^7 = 2^56 by norm_num, ← leValue_take, List.take_take]
  rfl

def bin48ToFelem (bs : List Byte) : Fin 7 → BitVec 64 := fun i =>
  if i.val < 6 then load64LE (bs.drop (7 * i.val)) &&& BitVec.ofNat 64 (2^56 - 1)
  else BitVec.ofNat 64 (leValue ((bs.drop 42).take 6))

def serialFelem (a : Felem) : Prop :=
  (∀ i : Fin 6, Within 56 (a i.castSucc)) ∧ Within 48 (a 6)

def felemBytes (a : Felem) : List Byte :=
  encodeLE 7 (a 0).toNat ++ encodeLE 7 (a 1).toNat ++
  encodeLE 7 (a 2).toNat ++ encodeLE 7 (a 3).toNat ++
  encodeLE 7 (a 4).toNat ++ encodeLE 7 (a 5).toNat ++ encodeLE 6 (a 6).toNat

@[simp] theorem felemBytes_length (a : Felem) : (felemBytes a).length = 48 := by
  simp [felemBytes]

theorem felemBytes_value (a : Felem) (ha : serialFelem a) :
    (leValue (felemBytes a) : ℤ) = eval7 a := by
  have h (i : Fin 6) : (a i.castSucc).toNat < 256^7 := by
    have := ha.1 i
    norm_num [Within] at this ⊢
    omega
  have ht : (a 6).toNat < 256^6 := by
    have := ha.2
    norm_num [Within] at this ⊢
    omega
  have hn (i : Fin 6) : ((a i.castSucc).toNat : ℤ) = a i.castSucc :=
    Int.toNat_of_nonneg (ha.1 i).1
  have hnt : ((a 6).toNat : ℤ) = a 6 := Int.toNat_of_nonneg ha.2.1
  have hna (i : Fin 7) : ((a i).toNat : ℤ) = a i := by
    fin_cases i
    exact hn 0
    exact hn 1
    exact hn 2
    exact hn 3
    exact hn 4
    exact hn 5
    exact hnt
  simp only [felemBytes, leValue_append, List.length_append, encodeLE_length,
    leValue_encodeLE]
  simp only [show (0 : Fin 7) = (0 : Fin 6).castSucc from rfl,
    show (1 : Fin 7) = (1 : Fin 6).castSucc from rfl,
    show (2 : Fin 7) = (2 : Fin 6).castSucc from rfl,
    show (3 : Fin 7) = (3 : Fin 6).castSucc from rfl,
    show (4 : Fin 7) = (4 : Fin 6).castSucc from rfl,
    show (5 : Fin 7) = (5 : Fin 6).castSucc from rfl,
    Nat.mod_eq_of_lt (h _), Nat.mod_eq_of_lt ht]
  push_cast
  simp only [hna]
  norm_num [eval7, radix]
  ring

theorem bin48ToFelem_value (bs : List Byte) (hl : bs.length = 48) :
    eval7 (fun i => unsigned (bin48ToFelem bs i)) = leValue bs := by
  have hs (k : ℕ) (hk : k ≤ 35) := leValue_split 7 (bs.drop k) (by simp [hl]; omega)
  have h0 := hs 0 (by omega)
  have h7 := hs 7 (by omega)
  have h14 := hs 14 (by omega)
  have h21 := hs 21 (by omega)
  have h28 := hs 28 (by omega)
  have h35 := hs 35 (by omega)
  simp only [List.drop_zero, List.drop_drop] at h0 h7 h14 h21 h28 h35
  have ht : (bs.drop 42).take 6 = bs.drop 42 := List.take_of_length_le (by simp [hl])
  have hb : leValue ((bs.drop 42).take 6) < 2^64 := by
    rw [ht]
    have := leValue_bound (bs.drop 42)
    have hb : (bs.drop 42).length = 6 := by simp [hl]
    rw [hb] at this
    exact this.trans_le (by norm_num)
  unfold eval7
  dsimp only
  have hlow (i : Fin 7) (hi : i.val < 6) :
      unsigned (bin48ToFelem bs i) = leValue ((bs.drop (7 * i.val)).take 7) := by
    simp only [bin48ToFelem, if_pos hi, unsigned, load64LE_low56]
  have htop : unsigned (bin48ToFelem bs 6) = leValue (bs.drop 42) := by
    change ((BitVec.ofNat 64 (leValue ((bs.drop 42).take 6))).toNat : ℤ) = _
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hb, ht]
  rw [hlow 0 (by decide), hlow 1 (by decide), hlow 2 (by decide),
    hlow 3 (by decide), hlow 4 (by decide), hlow 5 (by decide), htop]
  change (leValue (bs.take 7) : ℤ) + leValue ((bs.drop 7).take 7) * radix +
    leValue ((bs.drop 14).take 7) * radix^2 + leValue ((bs.drop 21).take 7) * radix^3 +
    leValue ((bs.drop 28).take 7) * radix^4 + leValue ((bs.drop 35).take 7) * radix^5 +
    leValue (bs.drop 42) * radix^6 = _
  have he :
    leValue (bs.take 7) + 256^7 * leValue ((bs.drop 7).take 7) +
    (256^7)^2 * leValue ((bs.drop 14).take 7) +
    (256^7)^3 * leValue ((bs.drop 21).take 7) +
    (256^7)^4 * leValue ((bs.drop 28).take 7) +
    (256^7)^5 * leValue ((bs.drop 35).take 7) +
    (256^7)^6 * leValue (bs.drop 42) = leValue bs := by
      norm_num at h0 h7 h14 h21 h28 h35 ⊢
      omega
  have hei := congrArg (fun n : ℕ => (n : ℤ)) he
  push_cast at hei
  norm_num [radix] at hei ⊢
  linarith

theorem bin48ToFelem_serial (bs : List Byte) :
    serialFelem (fun i => unsigned (bin48ToFelem bs i)) := by
  constructor
  · intro i
    have he : unsigned (bin48ToFelem bs i.castSucc) =
        leValue ((bs.drop (7 * i.val)).take 7) := by
      change (((if i.val < 6 then load64LE (bs.drop (7 * i.val)) &&&
        BitVec.ofNat 64 (2^56 - 1) else _) : BitVec 64).toNat : ℤ) = _
      rw [if_pos i.isLt, load64LE_low56]
    change Within 56 (unsigned (bin48ToFelem bs i.castSucc))
    rw [he]
    constructor
    · positivity
    · have h := leValue_take_bound 7 (bs.drop (7 * i.val))
      norm_num at h ⊢
      exact_mod_cast h
  · have hb := leValue_take_bound 6 (bs.drop 42)
    have h64 : leValue ((bs.drop 42).take 6) < 2^64 := by
      exact hb.trans_le (by norm_num)
    change Within 48 ((BitVec.ofNat 64 (leValue ((bs.drop 42).take 6))).toNat : ℤ)
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h64]
    constructor
    · positivity
    · norm_num at hb ⊢
      exact_mod_cast hb

theorem serialFelem_limb_bound (a : Felem) (ha : serialFelem a) (i : Fin 7) :
    Within 56 (a i) := by
  by_cases hi : i.val < 6
  · exact ha.1 ⟨i.val, hi⟩
  · have he : i = 6 := Fin.ext (by omega)
    subst i
    exact within_mono ha.2 (by decide)

theorem felemBytes_bin48ToFelem (bs : List Byte) (hl : bs.length = 48) :
    felemBytes (fun i => unsigned (bin48ToFelem bs i)) = bs := by
  apply leValue_injective
  · simp [hl]
  · have h := felemBytes_value _ (bin48ToFelem_serial bs)
    rw [bin48ToFelem_value bs hl] at h
    exact_mod_cast h

theorem bin48ToFelem_felemBytes (a : Felem) (ha : serialFelem a) :
    (fun i => unsigned (bin48ToFelem (felemBytes a) i)) = a := by
  apply eval7_injective
  · exact serialFelem_limb_bound _ (bin48ToFelem_serial _)
  · exact serialFelem_limb_bound a ha
  · rw [bin48ToFelem_value _ (felemBytes_length a), felemBytes_value a ha]

end P384
