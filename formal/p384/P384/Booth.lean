import P384.ScalarBits
import P384.GeneratedBooth

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
set_option exponentiation.threshold 2048

namespace P384

def boothValue (w : ℕ) : ℤ := ((w + 1) / 2 : ℕ) - 32 * (w / 32 : ℕ)

def signedDigit (sign digit : Byte) : ℤ :=
  if sign = 0 then digit.toNat else -(digit.toNat : ℤ)

theorem machineBoothRecode_correct (w : BitVec 6) :
    let result := machineBoothRecode (w.setWidth 8)
    result.1.toNat = w.toNat / 32 ∧ result.2.toNat ≤ 16 ∧
      signedDigit result.1 result.2 = boothValue w.toNat := by
  revert w
  decide

theorem machineBoothRecode_correct_byte (w : Byte) (hw : w.toNat < 64) :
    let result := machineBoothRecode w
    result.1.toNat ≤ 1 ∧ result.2.toNat ≤ 16 ∧
      signedDigit result.1 result.2 = boothValue w.toNat := by
  have he : (w.setWidth 6).setWidth 8 = w := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_setWidth]
    rw [Nat.mod_eq_of_lt hw, Nat.mod_eq_of_lt w.isLt]
  have h := machineBoothRecode_correct (w.setWidth 6)
  rw [he] at h
  have hv : (w.setWidth 6).toNat = w.toNat := by
    simp only [BitVec.toNat_setWidth]
    exact Nat.mod_eq_of_lt hw
  simp only [hv] at h
  exact ⟨by omega, h.2⟩

def boothChunk (n j : ℕ) : ℕ := n / 32^j % 32

def boothCarry (n : ℕ) : ℕ → ℕ
  | 0 => 0
  | j + 1 => boothChunk n j / 16

def boothWindow (n j : ℕ) : ℕ := 2 * boothChunk n j + boothCarry n j

theorem boothChunk_bound (n j : ℕ) : boothChunk n j < 32 := Nat.mod_lt _ (by decide)

theorem boothCarry_bound (n j : ℕ) : boothCarry n j < 2 := by
  cases j with
  | zero => simp [boothCarry]
  | succ j => have h := boothChunk_bound n j; simp only [boothCarry]; omega

theorem boothWindow_bound (n j : ℕ) : boothWindow n j < 64 := by
  have h := boothChunk_bound n j
  have hc := boothCarry_bound n j
  unfold boothWindow
  omega

theorem boothValue_window (n j : ℕ) : boothValue (boothWindow n j) =
    (boothChunk n j : ℤ) + boothCarry n j - 32 * boothCarry n (j + 1) := by
  have h := boothChunk_bound n j
  have hc := boothCarry_bound n j
  unfold boothValue boothWindow
  have hceil : (2 * boothChunk n j + boothCarry n j + 1) / 2 =
      boothChunk n j + boothCarry n j := by omega
  have hsign : (2 * boothChunk n j + boothCarry n j) / 32 = boothChunk n j / 16 := by omega
  rw [hceil, hsign, Nat.cast_add]
  rfl

def boothPrefix (n : ℕ) : ℕ → ℤ
  | 0 => 0
  | k + 1 => boothPrefix n k + (32 : ℤ)^k * boothValue (boothWindow n k)

theorem boothPrefix_value (n k : ℕ) :
    boothPrefix n k = (n % 32^k : ℕ) - (32 : ℤ)^k * boothCarry n k := by
  induction k with
  | zero => simp [boothPrefix, boothCarry, Nat.mod_one]
  | succ k ih =>
      rw [boothPrefix, ih, boothValue_window]
      have hmod : n % 32^(k + 1) = n % 32^k + 32^k * boothChunk n k := by
        rw [pow_succ, Nat.mod_mul]
        rfl
      rw [hmod, Nat.cast_add, Nat.cast_mul, Nat.cast_pow, pow_succ]
      ring

theorem boothPrefix_384 (n : ℕ) (hn : n < 2^384) : boothPrefix n 77 = n := by
  have hn' : n < 32^77 := hn.trans_le (by norm_num)
  have htop : boothCarry n 77 = 0 := by
    change (n / 32^76 % 32) / 16 = 0
    have h : n / 32^76 < 16 := (Nat.div_lt_iff_lt_mul (by positivity)).2 (by norm_num at hn ⊢; omega)
    omega
  rw [boothPrefix_value, htop, Nat.cast_zero, mul_zero, sub_zero, Nat.mod_eq_of_lt hn']

theorem boothCarry_bit (n j : ℕ) :
    boothCarry n j = scalarBit n ((5 * j : ℕ) - (1 : ℤ)) := by
  cases j with
  | zero => simp [boothCarry, scalarBit]
  | succ j =>
      have he : ((5 * (j + 1) : ℕ) : ℤ) - 1 = (5 * j + 4 : ℕ) := by omega
      rw [he, scalarBit_nat]
      have hp : (2 : ℕ)^(5 * j + 4) = 32^j * 16 := by
        rw [pow_add, pow_mul]; rfl
      simp only [boothCarry, boothChunk]
      rw [show (32 : ℕ) = 16 * 2 from rfl, Nat.mod_mul_right_div_self]
      rw [hp, Nat.div_div_eq_div_mul]

def boothBitWindow (n i : ℕ) : ℕ :=
  32 * scalarBit n (i + 4 : ℕ) + 16 * scalarBit n (i + 3 : ℕ) +
  8 * scalarBit n (i + 2 : ℕ) + 4 * scalarBit n (i + 1 : ℕ) +
  2 * scalarBit n i + scalarBit n ((i : ℤ) - 1)

theorem boothBitWindow_eq (n j : ℕ) : boothBitWindow n (5 * j) = boothWindow n j := by
  have h := binaryPrefix_shift 5 (5 * j) n
  rw [binaryPrefix_value] at h
  have hp : (2 : ℕ)^(5 * j) = 32^j := by rw [pow_mul]; rfl
  rw [hp] at h
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add] at h
  norm_num at h
  unfold boothBitWindow boothWindow boothChunk
  rw [boothCarry_bit]
  push_cast at h ⊢
  omega

end P384
