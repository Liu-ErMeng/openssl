import P384.BNImport
import P384.BitWidth

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option exponentiation.threshold 2048

namespace P384

theorem bnWordValue_append (xs ys : List (BitVec 64)) :
    bnWordValue (xs ++ ys) = bnWordValue xs + (2^64)^xs.length * bnWordValue ys := by
  induction xs with
  | nil => simp [bnWordValue]
  | cons x xs ih =>
      simp only [List.cons_append, bnWordValue, List.length_cons, ih, pow_succ]
      ring

theorem bnWordValue_bound (ws : List (BitVec 64)) : bnWordValue ws < 2^(64 * ws.length) := by
  induction ws with
  | nil => simp [bnWordValue]
  | cons w ws ih =>
      have hw := w.isLt
      rw [List.length_cons, Nat.mul_add, Nat.mul_one, pow_add]
      simp only [bnWordValue]
      omega

def bnCorrectTopLoop (ws : List (BitVec 64)) : ℕ → ℕ
  | 0 => 0
  | n + 1 => if ws.getD n 0 = 0 then bnCorrectTopLoop ws n else n + 1

theorem bnCorrectTopLoop_le (ws : List (BitVec 64)) (top : ℕ) : bnCorrectTopLoop ws top ≤ top := by
  induction top with
  | zero => rfl
  | succ n ih => simp only [bnCorrectTopLoop]; split <;> omega

theorem bnWordValue_take_succ (ws : List (BitVec 64)) (n : ℕ) (hn : n < ws.length) :
    bnWordValue (ws.take (n + 1)) = bnWordValue (ws.take n) + 2^(64 * n) * (ws.getD n 0).toNat := by
  rw [List.take_succ_eq_append_getElem hn, bnWordValue_append]
  simp only [List.length_take, Nat.min_eq_left (Nat.le_of_lt hn), bnWordValue,
    mul_zero, add_zero, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hn, Option.getD_some,
    ← pow_mul]

theorem bnCorrectTopLoop_value (ws : List (BitVec 64)) (top : ℕ) (ht : top ≤ ws.length) :
    bnWordValue (ws.take (bnCorrectTopLoop ws top)) = bnWordValue (ws.take top) := by
  induction top with
  | zero => rfl
  | succ n ih =>
      rw [bnCorrectTopLoop]
      by_cases hz : ws.getD n 0 = 0
      · rw [if_pos hz, ih (by omega), bnWordValue_take_succ ws n (by omega), hz]
        simp
      · rw [if_neg hz]

theorem bnCorrectTopLoop_normalized (ws : List (BitVec 64)) (top : ℕ) :
    bnCorrectTopLoop ws top = 0 ∨
      ws.getD (bnCorrectTopLoop ws top - 1) 0 ≠ 0 := by
  induction top with
  | zero => exact Or.inl rfl
  | succ n ih =>
      rw [bnCorrectTopLoop]
      split
      · exact ih
      · right
        simpa only [Nat.add_sub_cancel] using ‹ws.getD n 0 ≠ 0›

theorem size_shifted_add (high low k : ℕ) (hh : high ≠ 0) (hl : low < 2^k) :
    (low + 2^k * high).size = high.size + k := by
  have hd : (low + 2^k * high) / 2^k = high := by
    rw [Nat.add_mul_div_left _ _ (Nat.two_pow_pos k), Nat.div_eq_of_lt hl, zero_add]
  have hs := size_div_pow (low + 2^k * high) k
  rw [hd] at hs
  have hp : 0 < high.size := Nat.size_pos.2 (Nat.pos_of_ne_zero hh)
  omega

theorem bnNormalized_size (ws : List (BitVec 64)) (top : ℕ) (ht : top ≤ ws.length)
    (hn : top = 0 ∨ ws.getD (top - 1) 0 ≠ 0) :
    (bnWordValue (ws.take top)).size =
      if top = 0 then 0 else 64 * (top - 1) + (ws.getD (top - 1) 0).toNat.size := by
  cases top with
  | zero => simp [bnWordValue]
  | succ n =>
      have hnonzero : (ws.getD n 0).toNat ≠ 0 := by
        have h := hn.resolve_left (by omega)
        intro he
        apply h
        exact BitVec.eq_of_toNat_eq he
      have hl : bnWordValue (ws.take n) < 2^(64 * n) := by
        have hb := bnWordValue_bound (ws.take n)
        simpa only [List.length_take, Nat.min_eq_left (show n ≤ ws.length by omega)] using hb
      rw [bnWordValue_take_succ ws n (by omega), size_shifted_add _ _ _ hnonzero hl]
      simp only [Nat.add_sub_cancel, Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false, ↓reduceIte]
      omega

theorem bnRaw_size_upper (ws : List (BitVec 64)) (top : ℕ) (ht : top ≤ ws.length) :
    (bnWordValue (ws.take top)).size ≤
      if top = 0 then 0 else 64 * (top - 1) + (ws.getD (top - 1) 0).toNat.size := by
  by_cases hn : top = 0 ∨ ws.getD (top - 1) 0 ≠ 0
  · rw [bnNormalized_size ws top ht hn]
  · have ht0 : top ≠ 0 := fun h => hn (Or.inl h)
    have hz : ws.getD (top - 1) 0 = 0 := by
      by_contra h
      exact hn (Or.inr h)
    cases top with
    | zero => contradiction
    | succ n =>
        change ws.getD n 0 = 0 at hz
        rw [bnWordValue_take_succ ws n (by omega)]
        have hb := bnWordValue_bound (ws.take n)
        rw [List.length_take, Nat.min_eq_left (show n ≤ ws.length by omega)] at hb
        simp only [Nat.add_sub_cancel, hz, show (0 : BitVec 64).toNat = 0 from rfl,
          mul_zero, add_zero, Nat.size_zero, Nat.add_eq_zero_iff, Nat.one_ne_zero,
          and_false, ↓reduceIte]
        exact Nat.size_le.2 hb

theorem bnCorrectTopLoop_zero_iff (ws : List (BitVec 64)) (top : ℕ) (ht : top ≤ ws.length) :
    bnCorrectTopLoop ws top = 0 ↔ bnWordValue (ws.take top) = 0 := by
  let normalized := bnCorrectTopLoop ws top
  have hv := bnCorrectTopLoop_value ws top ht
  have hn := bnCorrectTopLoop_normalized ws top
  constructor
  · intro hz
    rw [hz] at hv
    simpa only [List.take_zero, bnWordValue] using hv.symm
  · intro hz
    rcases hn with he | he
    · exact he
    · by_contra ht0
      have hs := bnNormalized_size ws normalized ((bnCorrectTopLoop_le ws top).trans ht) (Or.inr he)
      rw [hv, hz, Nat.size_zero, if_neg ht0] at hs
      have hp : 0 < (ws.getD (normalized - 1) 0).toNat.size := by
        apply Nat.size_pos.2
        have hne : (ws.getD (normalized - 1) 0).toNat ≠ 0 := fun h => he (BitVec.eq_of_toNat_eq h)
        omega
      omega

def bnCorrectTopReads (ws : List (BitVec 64)) : ℕ → List ℕ
  | 0 => []
  | n + 1 => n :: (if ws.getD n 0 = 0 then bnCorrectTopReads ws n else [])

theorem bnCorrectTopReads_bound (ws : List (BitVec 64)) (top : ℕ) (ht : top ≤ ws.length) :
    ∀ j ∈ bnCorrectTopReads ws top, j < ws.length := by
  induction top with
  | zero => simp [bnCorrectTopReads]
  | succ n ih =>
      intro j hj
      simp only [bnCorrectTopReads, List.mem_cons] at hj
      rcases hj with rfl | hj
      · omega
      · split at hj
        · exact ih (by omega) j hj
        · simp at hj

structure BN64State where
  words : List (BitVec 64)
  top : ℕ
  negative : Bool
  flags : BitVec 32

def bnMagnitude (s : BN64State) : ℕ := bnWordValue (s.words.take s.top)

def bnCorrectTop (s : BN64State) (fixedTopMask : BitVec 32 := 0) : BN64State :=
  let top := bnCorrectTopLoop s.words s.top
  { s with
    top := top
    negative := if top = 0 then false else s.negative
    flags := s.flags &&& ~~~fixedTopMask }

theorem bnCorrectTop_value (s : BN64State) (ht : s.top ≤ s.words.length) :
    bnMagnitude (bnCorrectTop s) = bnMagnitude s := bnCorrectTopLoop_value s.words s.top ht

theorem bnCorrectTop_top_bound (s : BN64State) : (bnCorrectTop s).top ≤ s.top :=
  bnCorrectTopLoop_le s.words s.top

theorem bnCorrectTop_nonnegative_zero (s : BN64State) (ht : s.top ≤ s.words.length)
    (hz : bnMagnitude s = 0) : (bnCorrectTop s).negative = false := by
  have he := (bnCorrectTopLoop_zero_iff s.words s.top ht).2 hz
  simp only [bnCorrectTop, he, ↓reduceIte]

theorem bnCorrectTop_debug_flag_bits (s : BN64State) (i : Fin 32) :
    (bnCorrectTop s 65536).flags[i.val] = (s.flags[i.val] && decide (i.val ≠ 16)) := by
  change (s.flags &&& ~~~(65536 : BitVec 32))[i.val] = _
  rw [BitVec.getElem_and i.isLt, BitVec.getElem_not i.isLt]
  have he : (65536 : BitVec 32)[i.val] = decide (i.val = 16) := by
    change (2^16 : ℕ).testBit i.val = _
    simp only [Nat.testBit_two_pow, eq_comm]
  rw [he]
  congr 1
  simp

theorem bnCorrectTop_release_flags (s : BN64State) : (bnCorrectTop s).flags = s.flags := by
  change s.flags &&& ~~~(0 : BitVec 32) = s.flags
  rw [show ~~~(0 : BitVec 32) = BitVec.allOnes 32 by decide]
  exact BitVec.and_allOnes

end P384
