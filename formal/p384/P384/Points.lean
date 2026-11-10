import P384.Inversion
import Mathlib.Tactic.FieldSimp

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace P384

structure Jacobian (R : Type) where
  x : R
  y : R
  z : R
  deriving DecidableEq

def onCurve {R : Type} [CommRing R] (b : R) (q : Jacobian R) : Prop :=
  q.y^2 = q.x^3 - 3 * q.x * q.z^4 + b * q.z^6

def pointDouble {R : Type} [CommRing R] (q : Jacobian R) : Jacobian R :=
  let delta := q.z * q.z
  let gamma := q.y * q.y
  let beta := q.x * gamma
  let alpha := (q.x - delta) * (3 * (q.x + delta))
  let x := alpha * alpha - 8 * beta
  let z := (q.y + q.z)^2 - (delta + gamma)
  let y := alpha * (4 * beta - x) - 8 * gamma^2
  ⟨x, y, z⟩

def pointAddFormula {R : Type} [CommRing R] (p q : Jacobian R) : Jacobian R :=
  let u1 := p.x * q.z^2
  let u2 := q.x * p.z^2
  let s1 := p.y * q.z^3
  let s2 := q.y * p.z^3
  let h := u2 - u1
  let r := 2 * (s2 - s1)
  let i := (2 * h)^2
  let j := h * i
  let v := u1 * i
  let x := r^2 - j - 2 * v
  let y := r * (v - x) - 2 * s1 * j
  let z := ((p.z + q.z)^2 - p.z^2 - q.z^2) * h
  ⟨x, y, z⟩

def pointAdd {R : Type} [CommRing R] [DecidableEq R]
    (p q : Jacobian R) : Jacobian R :=
  if p.z ≠ 0 ∧ q.z ≠ 0 ∧ q.x * p.z^2 = p.x * q.z^2 ∧
      q.y * p.z^3 = p.y * q.z^3 then pointDouble p
  else if q.z = 0 then p else if p.z = 0 then q else pointAddFormula p q

theorem pointDouble_z {R : Type} [CommRing R] (q : Jacobian R) :
    (pointDouble q).z = 2 * q.y * q.z := by
  dsimp [pointDouble]
  ring

theorem pointDouble_onCurve {R : Type} [CommRing R] (b : R) (q : Jacobian R)
    (h : onCurve b q) : onCurve b (pointDouble q) := by
  unfold onCurve at *
  simp only [pointDouble]
  linear_combination 64 * q.y^6 * h

theorem pointDouble_infinity {R : Type} [CommRing R] (q : Jacobian R)
    (h : q.z = 0 ∨ q.y = 0) : (pointDouble q).z = 0 := by
  rw [pointDouble_z]
  rcases h with h | h <;> simp [h]

theorem pointAdd_left_infinity {R : Type} [CommRing R] [DecidableEq R]
    (p q : Jacobian R) (hp : p.z = 0) (hq : q.z ≠ 0) : pointAdd p q = q := by
  simp [pointAdd, hp, hq]

theorem pointAdd_right_infinity {R : Type} [CommRing R] [DecidableEq R]
    (p q : Jacobian R) (hq : q.z = 0) : pointAdd p q = p := by
  simp [pointAdd, hq]

theorem pointAdd_equal {R : Type} [CommRing R] [DecidableEq R]
    (p : Jacobian R) (hp : p.z ≠ 0) : pointAdd p p = pointDouble p := by
  simp [pointAdd, hp]

theorem pointAddFormula_z {R : Type} [CommRing R] (p q : Jacobian R) :
    (pointAddFormula p q).z = 2 * p.z * q.z * (q.x * p.z^2 - p.x * q.z^2) := by
  dsimp [pointAddFormula]
  ring

def affine {K : Type} [Field K] (q : Jacobian K) : K × K :=
  (q.x / q.z^2, q.y / q.z^3)

def affineDouble {K : Type} [Field K] (q : K × K) : K × K :=
  let slope := (3 * q.1^2 - 3) / (2 * q.2)
  let x := slope^2 - 2 * q.1
  (x, slope * (q.1 - x) - q.2)

def affineAdd {K : Type} [Field K] (p q : K × K) : K × K :=
  let slope := (q.2 - p.2) / (q.1 - p.1)
  let x := slope^2 - p.1 - q.1
  (x, slope * (p.1 - x) - p.2)

theorem pointDouble_affine {K : Type} [Field K] (q : Jacobian K)
    (h2 : (2 : K) ≠ 0) (hy : q.y ≠ 0) (hz : q.z ≠ 0) :
    affine (pointDouble q) = affineDouble (affine q) := by
  have hZ := pointDouble_z q
  have h8 : (8 : K) ≠ 0 := by convert pow_ne_zero 3 h2 using 1; norm_num
  have hslope : (3 * (q.x / q.z^2)^2 - 3) / (2 * (q.y / q.z^3)) =
      (3 * (q.x - q.z^2) * (q.x + q.z^2)) / (2 * q.y * q.z) := by
    apply (div_eq_div_iff (mul_ne_zero h2 (div_ne_zero hy (pow_ne_zero 3 hz)))
      (mul_ne_zero (mul_ne_zero h2 hy) hz)).2
    field_simp [hz]
    ring
  apply Prod.ext
  all_goals
    dsimp only [affine, affineDouble]
    rw [hslope]
    dsimp only [pointDouble] at *
    rw [hZ]
    field_simp (config := { maxDischargeDepth := 100 }) [h2, hy, hz, h8]
    ring

theorem pointAddFormula_affine {K : Type} [Field K] (p q : Jacobian K)
    (h2 : (2 : K) ≠ 0) (hp : p.z ≠ 0) (hq : q.z ≠ 0)
    (hx : q.x * p.z^2 - p.x * q.z^2 ≠ 0) :
    affine (pointAddFormula p q) = affineAdd (affine p) (affine q) := by
  have hZ := pointAddFormula_z p q
  have hd : q.x / q.z^2 - p.x / p.z^2 ≠ 0 := by
    intro h
    apply hx
    field_simp [hp, hq] at h
    linear_combination h
  have hslope : (q.y / q.z^3 - p.y / p.z^3) / (q.x / q.z^2 - p.x / p.z^2) =
      (q.y * p.z^3 - p.y * q.z^3) / (p.z * q.z * (q.x * p.z^2 - p.x * q.z^2)) := by
    apply (div_eq_div_iff hd (mul_ne_zero (mul_ne_zero hp hq) hx)).2
    field_simp [hp, hq]
    ring
  apply Prod.ext
  all_goals
    dsimp only [affine, affineAdd]
    rw [hslope]
    dsimp only [pointAddFormula] at *
    rw [hZ]
    field_simp (config := { maxDischargeDepth := 100 }) [h2, hp, hq, hx, hd]
    ring

end P384
