import P384.Basic
import Mathlib.NumberTheory.LucasPrimality
import Mathlib.Tactic.NormNum.Prime

set_option autoImplicit false
set_option maxRecDepth 16384

namespace P384
namespace Pratt

def powMod (modulus : ℕ) : ℕ → ℕ → ℕ → ℕ
  | 0, _, _ => 1
  | fuel + 1, base, exponent =>
      if exponent = 0 then 1
      else
        let half := powMod modulus fuel (base * base % modulus) (exponent / 2)
        if exponent % 2 = 0 then half else base * half % modulus

theorem powMod_correct (modulus : ℕ) (hm : 1 < modulus) (fuel base exponent : ℕ)
    (he : exponent < 2^fuel) : powMod modulus fuel base exponent = base^exponent % modulus := by
  induction fuel generalizing base exponent with
  | zero =>
      have hz : exponent = 0 := by simpa using he
      simp [hz, powMod, Nat.mod_eq_of_lt hm]
  | succ fuel ih =>
      by_cases hz : exponent = 0
      · simp [hz, powMod, Nat.mod_eq_of_lt hm]
      have hh : exponent / 2 < 2^fuel := by rw [Nat.pow_succ] at he; omega
      have hs : base^exponent = (base * base)^(exponent / 2) * base^(exponent % 2) := by
        rw [← Nat.pow_two, ← Nat.pow_mul, ← Nat.pow_add]
        congr 1
        omega
      by_cases hparity : exponent % 2 = 0
      · simp only [powMod, hz, hparity, if_false, if_true]
        rw [ih _ _ hh, hs, hparity, Nat.pow_zero, Nat.mul_one, ← Nat.pow_mod]
      · have hone : exponent % 2 = 1 := by omega
        simp only [powMod, hz, hparity, if_false]
        rw [ih _ _ hh, hs, hone, Nat.pow_one, ← Nat.pow_mod, Nat.mul_mod_mod, Nat.mul_comm]

theorem prime_dvd_list {q : ℕ} (hq : q.Prime) (factors : List ℕ)
    (hf : ∀ f ∈ factors, f.Prime) (hd : q ∣ factors.prod) : q ∈ factors := by
  induction factors with
  | nil => simp only [List.prod_nil] at hd; exact (hq.ne_one (Nat.eq_one_of_dvd_one hd)).elim
  | cons f fs ih =>
      rw [List.prod_cons] at hd
      rcases hq.dvd_mul.mp hd with h | h
      · have he : q = f := (Nat.prime_dvd_prime_iff_eq hq (hf f (by simp))).1 h
        simp [he]
      · exact List.mem_cons_of_mem _ (ih (fun g hg => hf g (by simp [hg])) h)

theorem prime_of_certificate (candidate witness bits : ℕ) (factors : List ℕ)
    (hp : 2 ≤ candidate) (hb : candidate - 1 < 2^bits)
    (hf : ∀ f ∈ factors, f.Prime) (hprod : factors.prod = candidate - 1)
    (hfull : powMod candidate bits witness (candidate - 1) = 1)
    (hproper : factors.Forall (fun f => powMod candidate bits witness ((candidate - 1) / f) ≠ 1)) :
    candidate.Prime := by
  have hfull' : witness^(candidate - 1) % candidate = 1 := by
    rw [← powMod_correct candidate (by omega) bits witness _ hb]
    exact hfull
  apply lucas_primality candidate (witness : ZMod candidate)
  · have hcast := congrArg (fun n : ℕ => (n : ZMod candidate)) hfull'
    simpa only [ZMod.natCast_mod, Nat.cast_pow, Nat.cast_one] using hcast
  · intro q hq hd
    have hmem : q ∈ factors := prime_dvd_list hq factors hf (hprod.symm ▸ hd)
    have hneq := (List.forall_iff_forall_mem.1 hproper) q hmem
    intro hbad
    have hmod := (ZMod.natCast_eq_natCast_iff' (witness^((candidate - 1) / q)) 1 candidate).1
      (by simpa only [Nat.cast_pow, Nat.cast_one] using hbad)
    rw [Nat.mod_eq_of_lt (by omega : 1 < candidate),
      ← powMod_correct candidate (by omega) bits witness _ ((Nat.div_le_self _ _).trans_lt hb)] at hmod
    exact hneq hmod

end Pratt
end P384
