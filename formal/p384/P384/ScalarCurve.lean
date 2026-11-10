import P384.CurveGroup
import P384.GeneratedScalarConstants
import P384.Serialization

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000
set_option exponentiation.threshold 2048

namespace P384

instance scalarP384Prime : Fact p.Prime := ⟨p_prime⟩

def nistB : ℕ := scalarCurveParams 2

def nistCurve : WeierstrassCurve.Affine (ZMod p) := shortCurve (nistB : ZMod p)

abbrev P384Point := nistCurve.Point

theorem scalarCurveParams_prime : scalarCurveParams 0 = p := by decide

theorem scalarCurveParams_a : scalarCurveParams 1 = p - 3 := by decide

def builtinCoordinate (idx : Fin 16) (coord : Fin 3) : Felem :=
  fun k => unsigned (builtinGeneratorWords idx ⟨coord.val * 7 + k.val, by omega⟩)

def builtinCoordinateNat (idx : Fin 16) (coord : Fin 3) : ℕ :=
  (eval7 (builtinCoordinate idx coord)).toNat

theorem builtinCoordinate_serial : ∀ idx coord, serialFelem (builtinCoordinate idx coord) := by
  unfold serialFelem Within
  decide

theorem builtinCoordinate_nonneg : ∀ idx coord, 0 ≤ eval7 (builtinCoordinate idx coord) := by decide

theorem builtinCoordinate_cast (idx : Fin 16) (coord : Fin 3) :
    (builtinCoordinateNat idx coord : ZMod p) = fieldValue (builtinCoordinate idx coord) := by
  rw [builtinCoordinateNat, fieldValue, ← Int.cast_natCast, Int.toNat_of_nonneg (builtinCoordinate_nonneg idx coord)]

theorem builtin_zero : ∀ coord, builtinCoordinateNat 0 coord = 0 := by decide

theorem builtin_affine_z : ∀ idx : Fin 15, builtinCoordinateNat idx.succ 2 = 1 := by decide

theorem builtin_curve_equation : ∀ idx : Fin 15,
    ((builtinCoordinateNat idx.succ 1)^2 + 3 * builtinCoordinateNat idx.succ 0) % p =
      ((builtinCoordinateNat idx.succ 0)^3 + nistB) % p := by decide

theorem builtin_nonzero_derivative : ∀ idx : Fin 15,
    (2 * builtinCoordinateNat idx.succ 1) % p ≠ 0 := by decide

theorem natCurvePoint_nonsingular (x y : ℕ)
    (heq : (y^2 + 3 * x) % p = (x^3 + nistB) % p) (hderiv : (2 * y) % p ≠ 0) :
    nistCurve.Nonsingular (x : ZMod p) (y : ZMod p) := by
  have he := congrArg (fun n : ℕ => (n : ZMod p)) heq
  have he' : (y : ZMod p)^2 + 3 * x = (x : ZMod p)^3 + nistB := by
    simpa only [ZMod.natCast_mod, Nat.cast_add, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat] using he
  have hy : (2 : ZMod p) * y ≠ 0 := by
    rw [← Nat.cast_ofNat, ← Nat.cast_mul]
    exact (ZMod.natCast_zmod_eq_zero_iff_dvd _ _).not.mpr
      (by simpa only [Nat.dvd_iff_mod_eq_zero] using hderiv)
  apply (WeierstrassCurve.Affine.nonsingular_iff _ _).2
  constructor
  · apply (WeierstrassCurve.Affine.equation_iff _ _).2
    change (y : ZMod p)^2 + 0 * x * y + 0 * y = (x : ZMod p)^3 + 0 * x^2 + -3 * x + nistB
    linear_combination he'
  · right
    change (y : ZMod p) ≠ -y - 0 * x - 0
    intro h
    apply hy
    linear_combination h

theorem builtin_nonsingular (idx : Fin 15) :
    nistCurve.Nonsingular (builtinCoordinateNat idx.succ 0 : ZMod p)
      (builtinCoordinateNat idx.succ 1 : ZMod p) :=
  natCurvePoint_nonsingular _ _ (builtin_curve_equation idx) (builtin_nonzero_derivative idx)

def builtinCurvePoint (idx : Fin 16) : P384Point :=
  if h : idx.val = 0 then 0 else
    WeierstrassCurve.Affine.Point.some (builtin_nonsingular ⟨idx.val - 1, by omega⟩)

theorem builtin_generator_coordinates :
    builtinCoordinateNat 1 0 = scalarCurveParams 3 ∧
      builtinCoordinateNat 1 1 = scalarCurveParams 4 := by decide

noncomputable def scalarMulP384 (ps : List (List Byte × P384Point))
    (g : Option (List Byte × P384Point)) : P384Point := scalarByteMul ps g

theorem scalarMulP384_correct (ps : List (List Byte × P384Point))
    (g : Option (List Byte × P384Point)) (hp : ∀ q ∈ ps, q.1.length = 48)
    (hg : ∀ q, g = some q → q.1.length = 48) :
    scalarMulP384 ps g = generatorValue (g.map (fun q => (leValue q.1, q.2))) +
      (ps.map (fun q => (leValue q.1 : ℤ) • q.2)).sum := scalarByteMul_correct ps g hp hg

end P384
