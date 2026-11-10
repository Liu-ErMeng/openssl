import P384.Generated

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 8192
set_option exponentiation.threshold 2048

namespace P384

def one : Felem := ![1, 0, 0, 0, 0, 0, 0]
def add (a b : Felem) : Felem := fun i => a i + b i
def scale (a : Felem) (k : ℤ) : Felem := fun i => a i * k
def neg (a : Felem) : Felem := fun i => pad64 i - a i
def sub64 (a b : Felem) : Felem := fun i => a i + pad64 i - b i
def sub128 (a b : Widefelem) : Widefelem := fun i => a i + pad128 i - b i

theorem one_correct : eval7 one = 1 := by decide

theorem add_correct (a b : Felem) : eval7 (add a b) = eval7 a + eval7 b := by
  simp only [eval7, add]
  ring

theorem scale_correct (a : Felem) (k : ℤ) : eval7 (scale a k) = eval7 a * k := by
  simp only [eval7, scale]
  ring

theorem mul_correct (a b : Felem) : eval13 (mul a b) = eval7 a * eval7 b := by
  simp [eval13, eval7, mul, Matrix.cons_val]
  ring

theorem square_eq_mul (a : Felem) : square a = mul a a := by
  funext i
  fin_cases i <;> norm_num [square, mul, Matrix.cons_val] <;> ring

theorem square_correct (a : Felem) : eval13 (square a) = eval7 a ^ 2 := by
  rw [square_eq_mul, mul_correct]
  ring

theorem pad64_value : eval7 pad64 = 2^12 * (p : ℤ) := by
  decide

theorem pad128_64_value : eval7 pad128_64 = 2^16 * (p : ℤ) := by
  decide

theorem pad128_value : eval13 pad128 = 2^415 * (p : ℤ) := by
  decide

theorem neg_value (a : Felem) : eval7 (neg a) = 2^12 * (p : ℤ) - eval7 a := by
  rw [← pad64_value]
  simp only [eval7, neg]
  ring

theorem neg_correct (a : Felem) : Congruent (eval7 (neg a)) (-eval7 a) := by
  apply congruent_of_multiple _ _ (2^12)
  rw [neg_value]
  ring

theorem sub64_value (a b : Felem) :
    eval7 (sub64 a b) = eval7 a - eval7 b + 2^12 * (p : ℤ) := by
  rw [← pad64_value]
  simp only [eval7, sub64]
  ring

theorem sub64_correct (a b : Felem) :
    Congruent (eval7 (sub64 a b)) (eval7 a - eval7 b) := by
  apply congruent_of_multiple _ _ (2^12)
  rw [sub64_value]
  ring

theorem sub128_correct (a b : Widefelem) :
    Congruent (eval13 (sub128 a b)) (eval13 a - eval13 b) := by
  apply congruent_of_multiple _ _ (2^415)
  calc
    eval13 (sub128 a b) = eval13 a - eval13 b + eval13 pad128 := by
      simp only [eval13, sub128]
      ring
    _ = eval13 a - eval13 b + (p : ℤ) * 2^415 := by rw [pad128_value]; ring

theorem neg_bounds (a : Felem)
    (ha : ∀ i, 0 ≤ a i ∧ a i < 2^60 - 2^52 - 2^4) :
    ∀ i, Within 61 (neg a i) := by
  intro i
  have h := ha i
  fin_cases i <;> norm_num [neg, pad64, Within, Matrix.cons_val] at * <;> omega

theorem mul_bounds (a b : Felem)
    (ha : ∀ i, Within 61 (a i)) (hb : ∀ i, Within 61 (b i)) :
    ∀ i, 0 ≤ mul a b i ∧ mul a b i < 2^128 - 2^125 := by
  have hab : ∀ i j : Fin 7,
      0 ≤ a i * b j ∧ a i * b j ≤ (2^61 - 1 : ℤ)^2 := by
    intro i j
    obtain ⟨ha0, ha1⟩ := ha i
    obtain ⟨hb0, hb1⟩ := hb j
    norm_num at ha1 hb1 ⊢
    constructor
    · exact mul_nonneg ha0 hb0
    · nlinarith [mul_nonneg (show 0 ≤ 2^61 - 1 - a i by omega)
          (show 0 ≤ 2^61 - 1 - b j by omega)]
  have h00 := hab (0 : Fin 7) (0 : Fin 7)
  have h01 := hab (0 : Fin 7) (1 : Fin 7)
  have h02 := hab (0 : Fin 7) (2 : Fin 7)
  have h03 := hab (0 : Fin 7) (3 : Fin 7)
  have h04 := hab (0 : Fin 7) (4 : Fin 7)
  have h05 := hab (0 : Fin 7) (5 : Fin 7)
  have h06 := hab (0 : Fin 7) (6 : Fin 7)
  have h10 := hab (1 : Fin 7) (0 : Fin 7)
  have h11 := hab (1 : Fin 7) (1 : Fin 7)
  have h12 := hab (1 : Fin 7) (2 : Fin 7)
  have h13 := hab (1 : Fin 7) (3 : Fin 7)
  have h14 := hab (1 : Fin 7) (4 : Fin 7)
  have h15 := hab (1 : Fin 7) (5 : Fin 7)
  have h16 := hab (1 : Fin 7) (6 : Fin 7)
  have h20 := hab (2 : Fin 7) (0 : Fin 7)
  have h21 := hab (2 : Fin 7) (1 : Fin 7)
  have h22 := hab (2 : Fin 7) (2 : Fin 7)
  have h23 := hab (2 : Fin 7) (3 : Fin 7)
  have h24 := hab (2 : Fin 7) (4 : Fin 7)
  have h25 := hab (2 : Fin 7) (5 : Fin 7)
  have h26 := hab (2 : Fin 7) (6 : Fin 7)
  have h30 := hab (3 : Fin 7) (0 : Fin 7)
  have h31 := hab (3 : Fin 7) (1 : Fin 7)
  have h32 := hab (3 : Fin 7) (2 : Fin 7)
  have h33 := hab (3 : Fin 7) (3 : Fin 7)
  have h34 := hab (3 : Fin 7) (4 : Fin 7)
  have h35 := hab (3 : Fin 7) (5 : Fin 7)
  have h36 := hab (3 : Fin 7) (6 : Fin 7)
  have h40 := hab (4 : Fin 7) (0 : Fin 7)
  have h41 := hab (4 : Fin 7) (1 : Fin 7)
  have h42 := hab (4 : Fin 7) (2 : Fin 7)
  have h43 := hab (4 : Fin 7) (3 : Fin 7)
  have h44 := hab (4 : Fin 7) (4 : Fin 7)
  have h45 := hab (4 : Fin 7) (5 : Fin 7)
  have h46 := hab (4 : Fin 7) (6 : Fin 7)
  have h50 := hab (5 : Fin 7) (0 : Fin 7)
  have h51 := hab (5 : Fin 7) (1 : Fin 7)
  have h52 := hab (5 : Fin 7) (2 : Fin 7)
  have h53 := hab (5 : Fin 7) (3 : Fin 7)
  have h54 := hab (5 : Fin 7) (4 : Fin 7)
  have h55 := hab (5 : Fin 7) (5 : Fin 7)
  have h56 := hab (5 : Fin 7) (6 : Fin 7)
  have h60 := hab (6 : Fin 7) (0 : Fin 7)
  have h61 := hab (6 : Fin 7) (1 : Fin 7)
  have h62 := hab (6 : Fin 7) (2 : Fin 7)
  have h63 := hab (6 : Fin 7) (3 : Fin 7)
  have h64 := hab (6 : Fin 7) (4 : Fin 7)
  have h65 := hab (6 : Fin 7) (5 : Fin 7)
  have h66 := hab (6 : Fin 7) (6 : Fin 7)
  intro i
  fin_cases i <;> norm_num [mul, Matrix.cons_val] <;> omega

theorem square_bounds (a : Felem) (ha : ∀ i, Within 61 (a i)) :
    ∀ i, 0 ≤ square a i ∧ square a i < 2^128 - 2^125 := by
  rw [square_eq_mul]
  exact mul_bounds a a ha ha

theorem square_doubling_fits (a : Felem) (ha : ∀ i, Within 61 (a i)) :
    ∀ i, Within 64 (2 * a i) := by
  intro i
  have h := ha i
  norm_num [Within] at *
  omega

end P384
