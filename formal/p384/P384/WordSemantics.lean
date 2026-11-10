import P384.Machine

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace P384

theorem unsigned_bounds {bits : ℕ} (x : BitVec bits) : Within bits (unsigned x) := by
  constructor
  · exact Int.ofNat_zero_le _
  · have h := x.isLt
    change (x.toNat : ℤ) < 2^bits
    exact_mod_cast h

theorem ofInt_unsigned {bits : ℕ} (x : BitVec bits) :
    BitVec.ofInt bits (unsigned x) = x := by
  simp [unsigned]

theorem eq_of_unsigned_eq {bits : ℕ} {x y : BitVec bits}
    (h : unsigned x = unsigned y) : x = y :=
  BitVec.eq_of_toNat_eq (Int.ofNat_inj.mp h)

theorem unsigned_shiftRight {bits : ℕ} (x : BitVec bits) (n : ℕ) :
    unsigned (x >>> n) = unsigned x / 2^n := by
  simp [unsigned, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]

theorem unsigned_shiftLeft {bits : ℕ} (x : BitVec bits) (n : ℕ) :
    unsigned (x <<< n) = (unsigned x * 2^n) % 2^bits := by
  simp [unsigned, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]

theorem ofInt_shiftLeft (bits : ℕ) (x : ℤ) (n : ℕ) :
    (BitVec.ofInt bits x) <<< n = BitVec.ofInt bits (x * 2^n) := by
  apply eq_of_unsigned_eq
  rw [unsigned_shiftLeft, unsigned_ofInt, unsigned_ofInt]
  simp [Int.mul_emod]

theorem within_div_pow {bits : ℕ} (x : ℤ) (h : Within bits x) (n : ℕ) :
    Within bits (x / 2^n) :=
  ⟨Int.ediv_nonneg h.1 (by positivity), (Int.ediv_le_self _ h.1).trans_lt h.2⟩

theorem ofInt_shiftRight (bits : ℕ) (x : ℤ) (h : Within bits x) (n : ℕ) :
    (BitVec.ofInt bits x) >>> n = BitVec.ofInt bits (x / 2^n) := by
  apply eq_of_unsigned_eq
  rw [unsigned_shiftRight, unsigned_ofInt_exact bits x h,
    unsigned_ofInt_exact bits _ (within_div_pow x h n)]

theorem unsigned_mask {bits : ℕ} (x : BitVec bits) (n : ℕ) (hn : n ≤ bits) :
    unsigned (x &&& BitVec.ofNat bits (2^n - 1)) = unsigned x % 2^n := by
  have hpow : (2 : ℕ)^n ≤ 2^bits := Nat.pow_le_pow_of_le Nat.one_lt_two hn
  have hpos : 0 < (2 : ℕ)^n := Nat.two_pow_pos n
  unfold unsigned
  rw [BitVec.toNat_and, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega),
    Nat.and_two_pow_sub_one_eq_mod]
  norm_cast

theorem ofInt_mask (bits : ℕ) (x : ℤ) (h : Within bits x) (n : ℕ) (hn : n ≤ bits) :
    BitVec.ofInt bits x &&& BitVec.ofNat bits (2^n - 1) =
      BitVec.ofInt bits (x % 2^n) := by
  have hpow : (2 : ℤ)^n ≤ 2^bits := by
    exact_mod_cast (Nat.pow_le_pow_of_le Nat.one_lt_two hn)
  have hm : Within bits (x % 2^n) :=
    ⟨Int.emod_nonneg _ (by positivity), (Int.emod_lt_of_pos _ (by positivity)).trans_le hpow⟩
  apply eq_of_unsigned_eq
  rw [unsigned_mask _ n hn, unsigned_ofInt_exact bits x h, unsigned_ofInt_exact bits _ hm]

theorem unsigned_setWidth {bits : ℕ} (x : BitVec bits) (target : ℕ) :
    unsigned (x.setWidth target) = unsigned x % 2^target := by
  simp [unsigned, BitVec.toNat_setWidth]

theorem unsigned_setWidth_ofInt (bits target : ℕ) (x : ℤ)
    (hs : Within bits x) (ht : Within target x) :
    unsigned ((BitVec.ofInt bits x).setWidth target) = x := by
  rw [unsigned_setWidth, unsigned_ofInt_exact bits x hs, Int.emod_eq_of_lt ht.1 ht.2]

theorem setWidth_ofInt_exact (bits target : ℕ) (x : ℤ)
    (hs : Within bits x) (ht : Within target x) :
    (BitVec.ofInt bits x).setWidth target = BitVec.ofInt target x := by
  apply eq_of_unsigned_eq
  rw [unsigned_setWidth_ofInt bits target x hs ht, unsigned_ofInt_exact target x ht]

theorem within_mono {small large : ℕ} {x : ℤ} (hx : Within small x) (h : small ≤ large) :
    Within large x := by
  refine ⟨hx.1, hx.2.trans_le ?_⟩
  exact_mod_cast (Nat.pow_le_pow_of_le Nat.one_lt_two h)

end P384
