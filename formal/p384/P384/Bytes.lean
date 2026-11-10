import P384.WordSemantics

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace P384

abbrev Byte := BitVec 8

def leValue : List Byte → ℕ
  | [] => 0
  | b :: bs => b.toNat + 256 * leValue bs

def encodeLE : ℕ → ℕ → List Byte
  | 0, _ => []
  | n + 1, x => BitVec.ofNat 8 x :: encodeLE n (x / 256)

@[simp] theorem encodeLE_length (n x : ℕ) : (encodeLE n x).length = n := by
  induction n generalizing x <;> simp [encodeLE, *]

theorem leValue_bound (bs : List Byte) : leValue bs < 256^bs.length := by
  induction bs with
  | nil => simp [leValue]
  | cons b bs ih =>
      have hb : b.toNat < 256 := b.isLt
      simp only [leValue, List.length_cons, pow_succ]
      omega

theorem leValue_take_bound (n : ℕ) (bs : List Byte) : leValue (bs.take n) < 256^n :=
  (leValue_bound _).trans_le
    (Nat.pow_le_pow_of_le (by decide) (List.length_take_le _ _))

theorem leValue_encodeLE (n x : ℕ) : leValue (encodeLE n x) = x % 256^n := by
  induction n generalizing x with
  | zero => simp [encodeLE, leValue, Nat.mod_one]
  | succ n ih =>
      simp only [encodeLE, leValue, ih, BitVec.toNat_ofNat]
      simpa only [pow_succ, Nat.mul_comm, Nat.pow_succ] using
        (Nat.mod_mul (a := 256) (b := 256^n) (x := x)).symm

theorem encodeLE_leValue (bs : List Byte) : encodeLE bs.length (leValue bs) = bs := by
  induction bs with
  | nil => rfl
  | cons b bs ih =>
      have hb : b.toNat < 256 := b.isLt
      have hd : (b.toNat + 256 * leValue bs) / 256 = leValue bs := by omega
      have hm : BitVec.ofNat 8 (b.toNat + 256 * leValue bs) = b := by
        apply BitVec.eq_of_toNat_eq
        simp only [BitVec.toNat_ofNat]
        change (b.toNat + 256 * leValue bs) % 256 = b.toNat
        omega
      simp only [List.length_cons, leValue, encodeLE, hd, hm, ih]

theorem leValue_injective (xs ys : List Byte) (hl : xs.length = ys.length)
    (hv : leValue xs = leValue ys) : xs = ys := by
  rw [← encodeLE_leValue xs, hl, hv, encodeLE_leValue]

theorem leValue_append (xs ys : List Byte) :
    leValue (xs ++ ys) = leValue xs + 256^xs.length * leValue ys := by
  induction xs with
  | nil => simp [leValue]
  | cons x xs ih =>
      simp only [List.cons_append, leValue, List.length_cons, ih, pow_succ]
      ring

theorem leValue_split (n : ℕ) (bs : List Byte) (hn : n ≤ bs.length) :
    leValue bs = leValue (bs.take n) + 256^n * leValue (bs.drop n) := by
  simpa only [List.take_append_drop, List.length_take, Nat.min_eq_left hn] using
    leValue_append (bs.take n) (bs.drop n)

theorem leValue_take (n : ℕ) (bs : List Byte) :
    leValue (bs.take n) = leValue bs % 256^n := by
  induction n generalizing bs with
  | zero => simp [leValue, Nat.mod_one]
  | succ n ih =>
      cases bs with
      | nil => simp [leValue]
      | cons b bs =>
          have hb : b.toNat < 256 := b.isLt
          simp only [List.take_succ_cons, leValue, ih]
          rw [pow_succ, Nat.mul_comm (256^n) 256, Nat.mod_mul]
          have hm : (b.toNat + 256 * leValue bs) % 256 = b.toNat := by omega
          have hd : (b.toNat + 256 * leValue bs) / 256 = leValue bs := by omega
          rw [hm, hd]

theorem leValue_drop (n : ℕ) (bs : List Byte) :
    leValue (bs.drop n) = leValue bs / 256^n := by
  have h := leValue_append (bs.take n) (bs.drop n)
  rw [List.take_append_drop] at h
  by_cases hn : n ≤ bs.length
  · rw [List.length_take, Nat.min_eq_left hn] at h
    have ht := leValue_bound (bs.take n)
    rw [List.length_take, Nat.min_eq_left hn] at ht
    have hp : 0 < 256^n := by positivity
    rw [h, Nat.add_mul_div_left _ _ hp, Nat.div_eq_of_lt ht, zero_add]
  · rw [List.drop_eq_nil_of_le (by omega), leValue]
    exact (Nat.div_eq_of_lt ((leValue_bound bs).trans_le
      (Nat.pow_le_pow_of_le (by decide) (by omega)))).symm

theorem encodeLE_append (n m x : ℕ) :
    encodeLE (n + m) x = encodeLE n x ++ encodeLE m (x / 256^n) := by
  apply leValue_injective
  · simp
  · rw [leValue_append, encodeLE_length, leValue_encodeLE, leValue_encodeLE,
      leValue_encodeLE, pow_add, Nat.mod_mul]

def byteAt (x i : ℕ) : Byte := BitVec.ofNat 8 (x / 256^i)

theorem encodeLE_get (n x i : ℕ) (hi : i < n) :
    (encodeLE n x)[i]'(by simpa using hi) = byteAt x i := by
  induction n generalizing x i with
  | zero => omega
  | succ n ih =>
      cases i with
      | zero => simp [encodeLE, byteAt]
      | succ i =>
          simp only [encodeLE, List.getElem_cons_succ]
          rw [ih _ _ (by omega)]
          simp only [byteAt, Nat.div_div_eq_div_mul, pow_succ]
          rw [Nat.mul_comm 256]

theorem byteAt_leValue (bs : List Byte) (i : ℕ) :
    byteAt (leValue bs) i = bs.getD i 0 := by
  rw [byteAt, ← leValue_drop]
  have h : BitVec.ofNat 8 (leValue (bs.drop i)) = (bs.drop i).getD 0 0 := by
    generalize bs.drop i = tail
    cases tail with
    | nil => rfl
    | cons b tail =>
        apply BitVec.eq_of_toNat_eq
        have hb : b.toNat < 256 := b.isLt
        simp only [leValue, BitVec.toNat_ofNat, List.getD_cons_zero]
        change (b.toNat + 256 * leValue tail) % 256 = b.toNat
        omega
  rw [h]
  simp only [List.getD_eq_getElem?_getD, List.getElem?_drop, Nat.add_zero]

theorem encodeLE_getD (n x i : ℕ) (hi : i < n) :
    (encodeLE n x).getD i 0 = byteAt x i := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by simpa using hi),
    Option.getD_some, encodeLE_get n x i hi]

end P384
