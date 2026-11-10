import P384.GeneratedZero
import P384.Representation

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000
set_option exponentiation.threshold 2048

namespace P384

theorem zeroMask_bounded (x : BitVec 64) (hx : unsigned x < 2^63) :
    zeroMask x = if x = 0 then BitVec.allOnes 64 else 0 := by
  have hn : x.toNat < 2^63 := by change (x.toNat : ℤ) < 2^63 at hx; exact_mod_cast hx
  let small := x.setWidth 63
  have hs : small.zeroExtend 64 = x := by
    apply BitVec.eq_of_toNat_eq
    simp only [small, BitVec.zeroExtend_eq_setWidth, BitVec.toNat_setWidth]
    rw [Nat.mod_eq_of_lt hn, Nat.mod_eq_of_lt x.isLt]
  have hz : small = 0 ↔ x = 0 := by
    constructor
    · intro h
      simpa only [h, BitVec.zeroExtend_eq_setWidth, BitVec.setWidth_zero] using hs.symm
    · intro h
      simp [small, h]
  simpa only [hs, hz] using zeroMask_correct small

theorem zeroPrime_small : ∀ i, Within 56 (zeroPrimeLimbs i) := by unfold Within; decide
theorem zeroPrime_value : eval7 zeroPrimeLimbs = (p : ℤ) := by decide

theorem zeroPrimeWords_unsigned : (fun i => unsigned (zeroPrimeWords i)) = zeroPrimeLimbs := by
  funext i
  exact unsigned_ofInt_exact 64 _ (within_mono (zeroPrime_small i) (by decide))

theorem limbOr_zero (a : LimbWords) : limbOr a = 0 ↔ a = fun _ => 0 := by
  simp only [BitVec.ofNat_eq_ofNat, limbOr, BitVec.or_eq_zero_iff]
  constructor
  · rintro ⟨⟨⟨⟨⟨⟨h0, h1⟩, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩
    funext i
    fin_cases i <;> assumption
  · intro h
    exact ⟨⟨⟨⟨⟨⟨congrFun h 0, congrFun h 1⟩, congrFun h 2⟩, congrFun h 3⟩,
      congrFun h 4⟩, congrFun h 5⟩, congrFun h 6⟩

theorem xorPrime_zero (a : LimbWords) : limbOr (xorPrime a) = 0 ↔ a = zeroPrimeWords := by
  rw [limbOr_zero]
  constructor
  · intro h
    funext i
    exact BitVec.xor_eq_zero_iff.1 (congrFun h i)
  · intro h
    subst a
    funext i
    exact BitVec.xor_self

theorem limbOr_small (a : LimbWords) (ha : ∀ i, (a i).toNat < 2^56) :
    (limbOr a).toNat < 2^56 := by
  simp only [limbOr, BitVec.toNat_or]
  exact Nat.or_lt_two_pow (Nat.or_lt_two_pow (Nat.or_lt_two_pow
    (Nat.or_lt_two_pow (Nat.or_lt_two_pow (Nat.or_lt_two_pow (ha 0) (ha 1)) (ha 2)) (ha 3))
      (ha 4)) (ha 5)) (ha 6)

theorem word_small_reduced (a : LimbWords) (ha : Reduced (fun i => unsigned (a i))) :
    ∀ i, (a i).toNat < 2^56 := by
  intro i
  have h := (reduced_limbs_small _ ha i).2
  change ((a i).toNat : ℤ) < 2^56 at h
  exact_mod_cast h

theorem zeroPrimeWords_small : ∀ i, (zeroPrimeWords i).toNat < 2^56 := by decide

theorem zero_aggregates_bounded (a : LimbWords) (ha : Reduced (fun i => unsigned (a i))) :
    unsigned (limbOr a) < 2^63 ∧ unsigned (limbOr (xorPrime a)) < 2^63 := by
  have hsmall := word_small_reduced a ha
  have hz := limbOr_small a hsmall
  have hxor : ∀ i, (xorPrime a i).toNat < 2^56 := by
    intro i
    simp only [xorPrime, BitVec.toNat_xor]
    exact Nat.xor_lt_two_pow (hsmall i) (zeroPrimeWords_small i)
  have hp := limbOr_small _ hxor
  constructor
  · change ((limbOr a).toNat : ℤ) < 2^63
    exact_mod_cast hz.trans (by decide : (2 : ℕ)^56 < 2^63)
  · change ((limbOr (xorPrime a)).toNat : ℤ) < 2^63
    exact_mod_cast hp.trans (by decide : (2 : ℕ)^56 < 2^63)

theorem reduced_zero_residue (a : Felem) (ha : Reduced a) :
    eval7 a % (p : ℤ) = 0 ↔ eval7 a = 0 ∨ eval7 a = (p : ℤ) := by
  have hv := reduced_value_bounds a ha
  norm_num [p] at hv ⊢
  omega

theorem wordValue_zero (a : LimbWords) (ha : Reduced (fun i => unsigned (a i))) :
    eval7 (fun i => unsigned (a i)) = 0 ↔ limbOr a = 0 := by
  rw [limbOr_zero]
  constructor
  · intro hv
    have he := eval7_injective (fun i => unsigned (a i)) (fun _ => 0)
      (reduced_limbs_small _ ha) (by intro i; norm_num [Within]) (by simpa [eval7] using hv)
    funext i
    apply eq_of_unsigned_eq
    exact congrFun he i
  · intro h
    rw [h]
    change eval7 (fun _ => (0 : ℤ)) = 0
    simp only [eval7, zero_mul, zero_add, add_zero]

theorem wordValue_prime (a : LimbWords) (ha : Reduced (fun i => unsigned (a i))) :
    eval7 (fun i => unsigned (a i)) = (p : ℤ) ↔ limbOr (xorPrime a) = 0 := by
  rw [xorPrime_zero]
  constructor
  · intro hv
    have he := eval7_injective (fun i => unsigned (a i)) zeroPrimeLimbs
      (reduced_limbs_small _ ha) zeroPrime_small (hv.trans zeroPrime_value.symm)
    funext i
    apply eq_of_unsigned_eq
    rw [congrFun he i, congrFun zeroPrimeWords_unsigned i]
  · intro h
    rw [h, zeroPrimeWords_unsigned, zeroPrime_value]

theorem machineIsZero_subtractions_defined (a : LimbWords)
    (ha : Reduced (fun i => unsigned (a i))) :
    (-2^63 ≤ unsigned (limbOr a) - 1 ∧ unsigned (limbOr a) - 1 < 2^63) ∧
      (-2^63 ≤ unsigned (limbOr (xorPrime a)) - 1 ∧ unsigned (limbOr (xorPrime a)) - 1 < 2^63) := by
  have h := zero_aggregates_bounded a ha
  have hz := (unsigned_bounds (limbOr a)).1
  have hp := (unsigned_bounds (limbOr (xorPrime a))).1
  norm_num at *
  omega

theorem machineIsZero_correct (a : LimbWords) (ha : Reduced (fun i => unsigned (a i))) :
    machineIsZero a =
      if eval7 (fun i => unsigned (a i)) % (p : ℤ) = 0 then BitVec.allOnes 64 else 0 := by
  have hb := zero_aggregates_bounded a ha
  have hres : eval7 (fun i => unsigned (a i)) % (p : ℤ) = 0 ↔
      limbOr a = 0 ∨ limbOr (xorPrime a) = 0 :=
    (reduced_zero_residue _ ha).trans (or_congr (wordValue_zero a ha) (wordValue_prime a ha))
  unfold machineIsZero
  rw [zeroMask_bounded _ hb.1, zeroMask_bounded _ hb.2]
  by_cases hz : limbOr a = 0 <;> by_cases hp : limbOr (xorPrime a) = 0
  all_goals
    simp only [BitVec.ofNat_eq_ofNat] at hz hp hres ⊢
    simp [hres, hz, hp]

theorem machineIsZeroInt_correct (a : LimbWords) (ha : Reduced (fun i => unsigned (a i))) :
    machineIsZeroInt a = if eval7 (fun i => unsigned (a i)) % (p : ℤ) = 0 then 1 else 0 := by
  unfold machineIsZeroInt
  rw [machineIsZero_correct a ha]
  split <;> decide

end P384
