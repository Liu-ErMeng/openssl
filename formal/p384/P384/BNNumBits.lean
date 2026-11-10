import P384.BNWordBits
import P384.BNNormalize
import P384.ConstantTime32

set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option exponentiation.threshold 2048

namespace P384

def bnNumBitsRaw (ws : List (BitVec 64)) (top : ℕ) : ℕ :=
  if top = 0 then 0 else 64 * (top - 1) + (machineBNNumBitsWord (ws.getD (top - 1) 0)).toNat

theorem bnNumBitsRaw_upper (ws : List (BitVec 64)) (top : ℕ) (ht : top ≤ ws.length) :
    (bnWordValue (ws.take top)).size ≤ bnNumBitsRaw ws top := by
  simpa only [bnNumBitsRaw, machineBNNumBitsWord_correct] using bnRaw_size_upper ws top ht

theorem bnNumBitsRaw_exact (ws : List (BitVec 64)) (top : ℕ) (ht : top ≤ ws.length)
    (hn : top = 0 ∨ ws.getD (top - 1) 0 ≠ 0) :
    bnNumBitsRaw ws top = (bnWordValue (ws.take top)).size := by
  simpa only [bnNumBitsRaw, machineBNNumBitsWord_correct] using (bnNormalized_size ws top ht hn).symm

theorem bnNumBitsRaw_correctTop (ws : List (BitVec 64)) (top : ℕ) (ht : top ≤ ws.length) :
    bnNumBitsRaw ws (bnCorrectTopLoop ws top) = (bnWordValue (ws.take top)).size := by
  rw [bnNumBitsRaw_exact ws _ ((bnCorrectTopLoop_le ws top).trans ht)
      (bnCorrectTopLoop_normalized ws top), bnCorrectTopLoop_value ws top ht]

theorem bnNumBitsRaw_bound (ws : List (BitVec 64)) (top : ℕ) : bnNumBitsRaw ws top ≤ 64 * top := by
  have hb := machineBNNumBitsWord_range (ws.getD (top - 1) 0)
  unfold bnNumBitsRaw
  split <;> omega

structure BNBitsCTState where
  ret : BitVec 32
  past : BitVec 32

def bnNumBitsCTStep (top j : ℕ) (w : BitVec 64) (s : BNBitsCTState) : BNBitsCTState :=
  let mask := constantTimeEq32 (BitVec.ofInt 32 ((top : ℤ) - 1)) (BitVec.ofNat 32 j)
  let ret := s.ret + ((64 : BitVec 32) &&& (~~~mask &&& ~~~s.past))
  let ret := ret + (machineBNNumBitsWord w &&& mask)
  ⟨ret, s.past ||| mask⟩

def bnNumBitsCTPrefix (ws : List (BitVec 64)) (top : ℕ) : ℕ → BNBitsCTState
  | 0 => ⟨0, 0⟩
  | j + 1 => bnNumBitsCTStep top j (ws.getD j 0) (bnNumBitsCTPrefix ws top j)

def bnCTPrefixCount (ws : List (BitVec 64)) (top j : ℕ) : ℕ :=
  if top = 0 ∨ j < top then 64 * j else bnNumBitsRaw ws top

def bnCTPrefixPast (top j : ℕ) : BitVec 32 :=
  if top ≠ 0 ∧ top ≤ j then BitVec.allOnes 32 else 0

theorem bnCTPrefixCount_bound (ws : List (BitVec 64)) (top j : ℕ) :
    bnCTPrefixCount ws top j ≤ 64 * j := by
  unfold bnCTPrefixCount
  split
  · rfl
  · have hb := bnNumBitsRaw_bound ws top
    omega

theorem bnNumBitsCTPrefix_refines (ws : List (BitVec 64)) (top n : ℕ)
    (ht : top < 2^31) (hn : n < 2^31) :
    bnNumBitsCTPrefix ws top n =
      ⟨BitVec.ofNat 32 (bnCTPrefixCount ws top n), bnCTPrefixPast top n⟩ := by
  have hcount (w : BitVec 64) : machineBNNumBitsWord w = BitVec.ofNat 32 w.toNat.size := by
    apply BitVec.eq_of_toNat_eq
    rw [machineBNNumBitsWord_correct, BitVec.toNat_ofNat]
    have hb : w.toNat.size ≤ 64 := Nat.size_le.2 w.isLt
    rw [Nat.mod_eq_of_lt (by omega)]
  have hzeroAnd (x : BitVec 32) : x &&& (0 : BitVec 32) = 0 := BitVec.and_zero
  have hzeroOr (x : BitVec 32) : (0 : BitVec 32) ||| x = x := BitVec.zero_or
  have hadd0 (x : BitVec 32) : x + (0 : BitVec 32) = x := BitVec.add_zero x
  have hnot0 : ~~~(0 : BitVec 32) = BitVec.allOnes 32 := by decide
  induction n with
  | zero =>
      have hz : top = 0 ∨ 0 < top := by omega
      simp [bnNumBitsCTPrefix, bnCTPrefixCount, bnCTPrefixPast, hz]
  | succ n ih =>
      rw [bnNumBitsCTPrefix, ih (by omega)]
      dsimp only [bnNumBitsCTStep]
      rw [constantTimeEq32_top_index top n ht (by omega)]
      by_cases hz : top = 0
      · subst top
        simp [bnCTPrefixCount, bnCTPrefixPast, hnot0, hzeroAnd, hadd0,
          ← BitVec.ofNat_add, Nat.mul_add]
      · by_cases hbefore : n + 1 < top
        · have hn0 : n < top := by omega
          have hne : top ≠ n + 1 := by omega
          simp [bnCTPrefixCount, bnCTPrefixPast, hz, hbefore, hn0, hne, hnot0, hzeroAnd, hadd0,
            ← BitVec.ofNat_add, Nat.mul_add, show ¬top ≤ n by omega, show ¬top ≤ n + 1 by omega]
        · by_cases hhit : top = n + 1
          · have hn0 : n < top := by omega
            simp only [if_pos hhit, bnCTPrefixCount, bnCTPrefixPast, hz, hn0,
              false_or, not_false_eq_true, and_true, and_false,
              show top ≤ n + 1 by omega, show ¬top ≤ n by omega, show ¬n + 1 < top by omega,
              ↓reduceIte, hnot0, BitVec.not_allOnes, hzeroAnd, hadd0, hzeroOr,
              BitVec.and_allOnes, BitVec.allOnes_and]
            have he : bnNumBitsRaw ws top = 64 * n + (ws.getD n 0).toNat.size := by
              rw [bnNumBitsRaw, if_neg hz, hhit, Nat.add_sub_cancel, machineBNNumBitsWord_correct]
            simp only [BitVec.and_zero, BitVec.add_zero, if_pos hz]
            rw [hcount, ← BitVec.ofNat_add, he]
          · have hpast : top ≤ n := by omega
            have hne : top ≠ n + 1 := hhit
            simp [bnCTPrefixCount, bnCTPrefixPast, hz, hne, hpast, show top ≤ n + 1 by omega,
              show ¬n < top by omega, show ¬n + 1 < top by omega, hnot0, hzeroAnd, hadd0]

def machineBNNumBitsCT (ws : List (BitVec 64)) (top : ℕ) : BitVec 32 :=
  let state := bnNumBitsCTPrefix ws top ws.length
  let mask := ~~~constantTimeEq32 (BitVec.ofInt 32 ((top : ℤ) - 1)) (BitVec.ofInt 32 (-1))
  state.ret &&& mask

theorem machineBNNumBitsCT_correct (ws : List (BitVec 64)) (top : ℕ)
    (ht : top ≤ ws.length) (hc : 64 * ws.length < 2^31) :
    (machineBNNumBitsCT ws top).toNat = bnNumBitsRaw ws top := by
  have hlen : ws.length < 2^31 := by omega
  have htop : top < 2^31 := by omega
  rw [machineBNNumBitsCT, bnNumBitsCTPrefix_refines ws top ws.length htop hlen,
    constantTimeEq32_top_zero top htop]
  by_cases hz : top = 0
  · subst top
    simp [bnCTPrefixCount, bnNumBitsRaw]
  · simp only [if_neg hz, BitVec.and_allOnes, bnCTPrefixCount,
      hz, show ¬ws.length < top by omega, or_self, ↓reduceIte]
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt]
    have hb := bnNumBitsRaw_bound ws top
    omega

def BN64Valid (s : BN64State) : Prop := s.top ≤ s.words.length ∧ 64 * s.words.length + 7 < 2^31

theorem bnExpand_capacity_safe (capacity : ℕ) (h : capacity ≤ (2^31 - 1) / (4 * 64)) :
    64 * capacity + 7 < 2^31 := by norm_num at h ⊢; omega

def machineBNNumBitsOrdinary (ws : List (BitVec 64)) (top : ℕ) : BitVec 32 :=
  if top = 0 then 0 else BitVec.ofNat 32 (top - 1) * (64 : BitVec 32) +
    machineBNNumBitsWord (ws.getD (top - 1) 0)

theorem machineBNNumBitsOrdinary_correct (ws : List (BitVec 64)) (top : ℕ)
    (ht : top ≤ ws.length) (hc : 64 * ws.length < 2^31) :
    (machineBNNumBitsOrdinary ws top).toNat = bnNumBitsRaw ws top := by
  by_cases hz : top = 0
  · simp [machineBNNumBitsOrdinary, bnNumBitsRaw, hz]
  · have hword := machineBNNumBitsWord_range (ws.getD (top - 1) 0)
    simp only [machineBNNumBitsOrdinary, bnNumBitsRaw, if_neg hz, BitVec.toNat_add,
      BitVec.toNat_mul, BitVec.toNat_ofNat, show (64 : BitVec 32).toNat = 64 from rfl]
    rw [Nat.mod_eq_of_lt (show top - 1 < 2^32 by omega),
      Nat.mod_eq_of_lt (show (top - 1) * 64 < 2^32 by omega),
      Nat.mod_eq_of_lt (show (top - 1) * 64 + (machineBNNumBitsWord (ws.getD (top - 1) 0)).toNat < 2^32 by omega)]
    omega

def machineBNNumBits (s : BN64State) : BitVec 32 :=
  if s.flags &&& (4 : BitVec 32) ≠ 0 then machineBNNumBitsCT s.words s.top
  else machineBNNumBitsOrdinary s.words s.top

theorem machineBNNumBits_correct (s : BN64State) (hs : BN64Valid s) :
    (machineBNNumBits s).toNat = bnNumBitsRaw s.words s.top := by
  unfold machineBNNumBits
  split
  · exact machineBNNumBitsCT_correct s.words s.top hs.1 (by have h := hs.2; omega)
  · exact machineBNNumBitsOrdinary_correct s.words s.top hs.1 (by have h := hs.2; omega)

theorem bnCorrectTop_valid (s : BN64State) (hs : BN64Valid s) : BN64Valid (bnCorrectTop s) :=
  ⟨(bnCorrectTop_top_bound s).trans hs.1, hs.2⟩

theorem machineBNNumBits_normalized (s : BN64State) (hs : BN64Valid s) :
    (machineBNNumBits (bnCorrectTop s)).toNat = (bnMagnitude s).size := by
  rw [machineBNNumBits_correct _ (bnCorrectTop_valid s hs)]
  exact bnNumBitsRaw_correctTop s.words s.top hs.1

theorem machineBNNumBits_upper (s : BN64State) (hs : BN64Valid s) :
    (bnMagnitude s).size ≤ (machineBNNumBits s).toNat := by
  rw [machineBNNumBits_correct s hs]
  exact bnNumBitsRaw_upper s.words s.top hs.1

theorem machineBNNumBits_signed (s : BN64State) (hs : BN64Valid s) :
    (machineBNNumBits s).toInt = ((machineBNNumBits s).toNat : ℤ) ∧
      (machineBNNumBits s).toNat + 7 < 2^31 := by
  have hb := bnNumBitsRaw_bound s.words s.top
  have ht := hs.1
  have hc := hs.2
  rw [← machineBNNumBits_correct s hs] at hb
  constructor
  · apply BitVec.toInt_eq_toNat_of_lt
    omega
  · omega

theorem bnNumBitsCTPrefix_signed (ws : List (BitVec 64)) (top n : ℕ)
    (ht : top ≤ ws.length) (hn : n ≤ ws.length) (hc : 64 * ws.length < 2^31) :
    (bnNumBitsCTPrefix ws top n).ret.toNat ≤ 64 * n ∧
      (bnNumBitsCTPrefix ws top n).ret.toInt = ((bnNumBitsCTPrefix ws top n).ret.toNat : ℤ) := by
  have hp := bnCTPrefixCount_bound ws top n
  rw [bnNumBitsCTPrefix_refines ws top n (by omega) (by omega)]
  have hv : (BitVec.ofNat 32 (bnCTPrefixCount ws top n)).toNat = bnCTPrefixCount ws top n := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  constructor
  · exact hv.le.trans hp
  · apply BitVec.toInt_eq_toNat_of_lt
    change 2 * (BitVec.ofNat 32 (bnCTPrefixCount ws top n)).toNat < 2^32
    rw [hv]
    omega

end P384
