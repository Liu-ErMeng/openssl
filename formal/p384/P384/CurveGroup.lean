import P384.Points
import P384.ScalarMul
import P384.Prime
import Mathlib.AlgebraicGeometry.EllipticCurve.Group

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192

namespace P384

def shortCurve {K : Type} [CommRing K] (b : K) : WeierstrassCurve.Affine K :=
  ⟨0, 0, 0, -3, b⟩

def Represents {K : Type} [Field K] (b : K) (q : Jacobian K) : (shortCurve b).Point → Prop
  | .zero => q.z = 0
  | @WeierstrassCurve.Affine.Point.some _ _ _ x y _ => q.z ≠ 0 ∧ affine q = (x, y)

theorem represents_functional {K : Type} [Field K] (b : K) (q : Jacobian K)
    (P Q : (shortCurve b).Point) (hp : Represents b q P) (hq : Represents b q Q) : P = Q := by
  cases P with
  | zero =>
      cases Q with
      | zero => rfl
      | some hQ => exact False.elim (hq.1 hp)
  | @some x y hP =>
      cases Q with
      | zero => exact False.elim (hp.1 hq)
      | @some u v hQ =>
          have he := hp.2.symm.trans hq.2
          have hx := congrArg Prod.fst he
          have hy := congrArg Prod.snd he
          dsimp at hx hy
          subst u
          subst v
          rfl

theorem represents_scaled {K : Type} [Field K] (b : K) (q : Jacobian K) (x y : K)
    (h : (shortCurve b).Nonsingular x y) (hz : q.z ≠ 0)
    (hx : q.x = x * q.z^2) (hy : q.y = y * q.z^3) :
    Represents b q (WeierstrassCurve.Affine.Point.some h) := by
  refine ⟨hz, ?_⟩
  apply Prod.ext
  · exact (div_eq_iff (pow_ne_zero 2 hz)).2 hx
  · exact (div_eq_iff (pow_ne_zero 3 hz)).2 hy

theorem shortCurve_negY {K : Type} [Field K] (b x y : K) :
    (shortCurve b).negY x y = -y := by simp [shortCurve, WeierstrassCurve.Affine.negY]

def jacobianNeg {K : Type} [Neg K] (q : Jacobian K) : Jacobian K := ⟨q.x, -q.y, q.z⟩

theorem represents_neg {K : Type} [Field K] (b : K) (q : Jacobian K)
    (P : (shortCurve b).Point) (hr : Represents b q P) : Represents b (jacobianNeg q) (-P) := by
  cases P with
  | zero => exact hr
  | @some x y hP =>
      obtain ⟨hz, ha⟩ := hr
      constructor
      · exact hz
      · change affine (jacobianNeg q) = (x, (shortCurve b).negY x y)
        rw [shortCurve_negY]
        have hx := congrArg Prod.fst ha
        have hy := congrArg Prod.snd ha
        change q.y / q.z^3 = y at hy
        apply Prod.ext
        · exact hx
        · change -q.y / q.z^3 = -y
          rw [neg_div, hy]

theorem shortCurve_not_self_neg {K : Type} [Field K] (b x y : K)
    (h2 : (2 : K) ≠ 0) (hy : y ≠ 0) : y ≠ (shortCurve b).negY x y := by
  rw [shortCurve_negY]
  intro h
  have hz : 2 * y = 0 := by linear_combination h
  exact (mul_ne_zero h2 hy) hz

theorem shortCurve_double_formula {K : Type} [Field K] (b x y : K)
    (h2 : (2 : K) ≠ 0) (hy : y ≠ 0) :
    affineDouble (x, y) =
      ((shortCurve b).addX x x ((shortCurve b).slope x x y y),
       (shortCurve b).addY x x y ((shortCurve b).slope x x y y)) := by
  rw [WeierstrassCurve.Affine.slope_of_Y_ne rfl (shortCurve_not_self_neg b x y h2 hy)]
  simp only [shortCurve, WeierstrassCurve.Affine.addX, WeierstrassCurve.Affine.addY,
    WeierstrassCurve.Affine.negY, WeierstrassCurve.Affine.negAddY, affineDouble]
  have hd : y - (-y - 0 * x - 0) = 2 * y := by ring
  rw [hd]
  apply Prod.ext <;> dsimp <;> ring

theorem represents_double {K : Type} [Field K] (b : K) (q : Jacobian K)
    (P : (shortCurve b).Point) (hr : Represents b q P) (h2 : (2 : K) ≠ 0) :
    Represents b (pointDouble q) (P + P) := by
  cases P with
  | zero =>
      change q.z = 0 at hr
      change Represents b (pointDouble q) (0 + 0 : (shortCurve b).Point)
      rw [add_zero]
      exact pointDouble_infinity q (Or.inl hr)
  | @some x y hP =>
      obtain ⟨hz, ha⟩ := hr
      by_cases hy : y = 0
      · have hqy : q.y = 0 := by
          have h := congrArg Prod.snd ha
          change q.y / q.z^3 = y at h
          rw [hy] at h
          exact (div_eq_zero_iff).mp h |>.resolve_right (pow_ne_zero 3 hz)
        have he : y = (shortCurve b).negY x y := by rw [shortCurve_negY, hy, neg_zero]
        rw [WeierstrassCurve.Affine.Point.add_self_of_Y_eq he]
        exact pointDouble_infinity q (Or.inr hqy)
      · have hqy : q.y ≠ 0 := by
          intro he
          have h := congrArg Prod.snd ha
          simp [affine, he] at h
          exact hy h.symm
        rw [WeierstrassCurve.Affine.Point.add_self_of_Y_ne (shortCurve_not_self_neg b x y h2 hy)]
        constructor
        · rw [pointDouble_z]
          exact mul_ne_zero (mul_ne_zero h2 hqy) hz
        · rw [pointDouble_affine q h2 hqy hz, ha, shortCurve_double_formula b x y h2 hy]

theorem scaled_coordinate_iff {K : Type} [Field K] (a b u v : K)
    (hu : u ≠ 0) (hv : v ≠ 0) (k : ℕ) :
    b * u^k = a * v^k ↔ b / v^k = a / u^k :=
  (div_eq_div_iff (pow_ne_zero k hv) (pow_ne_zero k hu)).symm

theorem shortCurve_add_formula {K : Type} [Field K] (b x y u v : K) (hx : x ≠ u) :
    affineAdd (x, y) (u, v) =
      ((shortCurve b).addX x u ((shortCurve b).slope x u y v),
       (shortCurve b).addY x u y ((shortCurve b).slope x u y v)) := by
  rw [WeierstrassCurve.Affine.slope_of_X_ne hx]
  have hs : (y - v) / (x - u) = (v - y) / (u - x) := by
    apply (div_eq_div_iff (sub_ne_zero.mpr hx) (sub_ne_zero.mpr hx.symm)).2
    ring
  rw [hs]
  simp only [affineAdd, shortCurve, WeierstrassCurve.Affine.addX,
    WeierstrassCurve.Affine.addY, WeierstrassCurve.Affine.negY,
    WeierstrassCurve.Affine.negAddY]
  apply Prod.ext <;> dsimp <;> ring

theorem represents_add {K : Type} [Field K] [DecidableEq K] (b : K) (p q : Jacobian K)
    (P Q : (shortCurve b).Point) (hp : Represents b p P) (hq : Represents b q Q)
    (h2 : (2 : K) ≠ 0) : Represents b (pointAdd p q) (P + Q) := by
  cases P with
  | zero =>
      change p.z = 0 at hp
      change Represents b (pointAdd p q) (0 + Q : (shortCurve b).Point)
      rw [zero_add]
      cases Q with
      | zero =>
          change q.z = 0 at hq
          rw [pointAdd_right_infinity p q hq]
          exact hp
      | some hQ =>
          rw [pointAdd_left_infinity p q hp hq.1]
          exact hq
  | @some x y hP =>
      cases Q with
      | zero =>
          change q.z = 0 at hq
          change Represents b (pointAdd p q) (WeierstrassCurve.Affine.Point.some hP + 0)
          rw [add_zero, pointAdd_right_infinity p q hq]
          exact hp
      | @some u v hQ =>
          obtain ⟨hpz, hpa⟩ := hp
          obtain ⟨hqz, hqa⟩ := hq
          have hxe : q.x * p.z^2 = p.x * q.z^2 ↔ u = x := by
            rw [scaled_coordinate_iff p.x q.x p.z q.z hpz hqz 2]
            change (affine q).1 = (affine p).1 ↔ u = x
            rw [hpa, hqa]
          have hye : q.y * p.z^3 = p.y * q.z^3 ↔ v = y := by
            rw [scaled_coordinate_iff p.y q.y p.z q.z hpz hqz 3]
            change (affine q).2 = (affine p).2 ↔ v = y
            rw [hpa, hqa]
          by_cases hx : u = x
          · subst u
            by_cases hy : v = y
            · subst v
              rw [pointAdd, if_pos ⟨hpz, hqz, hxe.mpr rfl, hye.mpr rfl⟩]
              exact represents_double b p _ ⟨hpz, hpa⟩ h2
            · have he1 := (WeierstrassCurve.Affine.equation_iff (W' := shortCurve b) x y).mp hP.1
              have he2 := (WeierstrassCurve.Affine.equation_iff (W' := shortCurve b) x v).mp hQ.1
              simp only [shortCurve] at he1 he2
              have hm : (y - v) * (y + v) = 0 := by linear_combination he1 - he2
              have hsum : y + v = 0 := (mul_eq_zero.mp hm).resolve_left (sub_ne_zero.mpr (Ne.symm hy))
              have hn : y = (shortCurve b).negY x v := by
                rw [shortCurve_negY]
                exact eq_neg_of_add_eq_zero_left hsum
              rw [WeierstrassCurve.Affine.Point.add_of_Y_eq rfl hn]
              have hc : ¬(p.z ≠ 0 ∧ q.z ≠ 0 ∧ q.x * p.z^2 = p.x * q.z^2 ∧
                  q.y * p.z^3 = p.y * q.z^3) := fun h => hy (hye.mp h.2.2.2)
              rw [pointAdd, if_neg hc, if_neg hqz, if_neg hpz]
              change (pointAddFormula p q).z = 0
              rw [pointAddFormula_z, sub_eq_zero.mpr (hxe.mpr rfl), mul_zero]
          · have hproj : q.x * p.z^2 - p.x * q.z^2 ≠ 0 :=
              sub_ne_zero.mpr (fun h => hx (hxe.mp h))
            have hc : ¬(p.z ≠ 0 ∧ q.z ≠ 0 ∧ q.x * p.z^2 = p.x * q.z^2 ∧
                q.y * p.z^3 = p.y * q.z^3) := fun h => hx (hxe.mp h.2.2.1)
            rw [pointAdd, if_neg hc, if_neg hqz, if_neg hpz,
              WeierstrassCurve.Affine.Point.add_of_X_ne (Ne.symm hx)]
            constructor
            · rw [pointAddFormula_z]
              exact mul_ne_zero (mul_ne_zero (mul_ne_zero h2 hpz) hqz) hproj
            · rw [pointAddFormula_affine p q h2 hpz hqz hproj, hpa, hqa,
                shortCurve_add_formula b x y u v (Ne.symm hx)]

end P384
