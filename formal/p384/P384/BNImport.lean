import P384.BNBytes

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace P384

def bnWordValue : List (BitVec 64) → ℕ
  | [] => 0
  | w :: ws => w.toNat + 2^64 * bnWordValue ws

def bnImportWords : ℕ → List Byte → List (BitVec 64)
  | 0, _ => []
  | n + 1, bs => bnPack (bs.take 8) :: bnImportWords n (bs.drop 8)

@[simp] theorem bnImportWords_length (n : ℕ) (bs : List Byte) :
    (bnImportWords n bs).length = n := by
  induction n generalizing bs <;> simp [bnImportWords, *]

theorem bnImportWords_value (n : ℕ) (bs : List Byte) :
    bnWordValue (bnImportWords n bs) = leValue bs % 256^(8 * n) := by
  induction n generalizing bs with
  | zero => simp [bnImportWords, bnWordValue, Nat.mod_one]
  | succ n ih =>
      simp only [bnImportWords, bnWordValue, bnPack_correct _ (List.length_take_le _ _),
        ih, leValue_take, leValue_drop]
      have hp : (256 : ℕ)^(8 * (n + 1)) = 256^8 * 256^(8 * n) := by
        rw [Nat.mul_add, Nat.mul_one, pow_add, Nat.mul_comm]
      rw [hp, Nat.mod_mul]
      rfl

theorem bnImportWords_exact (n : ℕ) (bs : List Byte) (hl : bs.length ≤ 8 * n) :
    bnWordValue (bnImportWords n bs) = leValue bs := by
  rw [bnImportWords_value, Nat.mod_eq_of_lt]
  exact (leValue_bound bs).trans_le (Nat.pow_le_pow_of_le (by decide) hl)

def trimLE (bs : List Byte) : List Byte := (bs.reverse.dropWhile (· == 0)).reverse

theorem trimLE_value (bs : List Byte) : leValue (trimLE bs) = leValue bs := by
  induction bs using List.reverseRecOn with
  | nil => rfl
  | append_singleton bs b ih =>
      by_cases hb : b = 0
      · subst b
        simpa [trimLE, leValue_append, leValue] using ih
      · have hb' : (b == (0 : Byte)) = false := by simpa only [beq_eq_false_iff_ne] using hb
        simp only [trimLE, List.reverse_append, List.reverse_cons, List.reverse_nil,
          List.cons_append, List.nil_append, List.dropWhile_cons, hb', Bool.false_eq_true, ↓reduceIte,
          List.reverse_reverse]

theorem trimLE_length (bs : List Byte) : (trimLE bs).length ≤ bs.length := by
  simpa [trimLE] using
    (List.dropWhile_sublist (l := bs.reverse) (· == (0 : Byte))).length_le

theorem bnImportWords48_value (bs : List Byte) (hl : bs.length = 48) :
    bnWordValue (bnImportWords 6 (trimLE bs)) = leValue bs := by
  rw [bnImportWords_exact _ _ ((trimLE_length bs).trans (by omega)), trimLE_value]

def bnImportCount (len : ℕ) : ℕ := if len = 0 then 0 else (len - 1) / 8 + 1

theorem bnImportCount_covers (len : ℕ) : len ≤ 8 * bnImportCount len := by
  unfold bnImportCount
  split <;> omega

def bnImportLE (bs : List Byte) : List (BitVec 64) :=
  let trimmed := trimLE bs
  bnImportWords (bnImportCount trimmed.length) trimmed

theorem bnImportLE_value (bs : List Byte) : bnWordValue (bnImportLE bs) = leValue bs := by
  rw [bnImportLE, bnImportWords_exact _ _ (bnImportCount_covers _), trimLE_value]

def bnImportSign (bs : List Byte) (oldNegative : Bool) : Bool :=
  if bs.length = 0 then false
  else if (trimLE bs).length = 0 then oldNegative
  else false

theorem bnImportSign_nonnegative (bs : List Byte) : bnImportSign bs false = false := by
  simp [bnImportSign]

theorem bnImportSign_zero_reuse (bs : List Byte) (hl : bs.length ≠ 0)
    (hz : (trimLE bs).length = 0) : bnImportSign bs true = true := by
  simp only [bnImportSign, if_neg hl, if_pos hz]

theorem bnImportSign_zero48 : bnImportSign (List.replicate 48 0) true = true := by
  decide

end P384
