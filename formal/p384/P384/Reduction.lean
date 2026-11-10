import P384.Field

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

namespace P384

theorem reduce_exact (a : Widefelem) :
    eval7 (reduce a) = eval13 a + (p : ℤ) * (2^76 - (reduceTrace a).quotient) := by
  simp only [reduce, reduceTrace, eval7, eval13, Matrix.cons_val, Matrix.cons_val_zero,
    Matrix.cons_val_succ, Matrix.head_cons, Matrix.tail_cons]
  simp only [Int.emod_def]
  norm_num [radix, p]
  ring

theorem reduce_correct (a : Widefelem) : Congruent (eval7 (reduce a)) (eval13 a) :=
  congruent_of_multiple _ _ _ (reduce_exact a)

def mulReduce (a b : Felem) : Felem := reduce (mul a b)
def squareReduce (a : Felem) : Felem := reduce (square a)

theorem mulReduce_correct (a b : Felem) :
    Congruent (eval7 (mulReduce a b)) (eval7 a * eval7 b) := by
  unfold mulReduce
  rw [← mul_correct]
  exact reduce_correct _

theorem squareReduce_correct (a : Felem) :
    Congruent (eval7 (squareReduce a)) (eval7 a ^ 2) := by
  unfold squareReduce
  rw [← square_correct]
  exact reduce_correct _

theorem mulReduce_bounds (a b : Felem)
    (ha : ∀ i, Within 61 (a i)) (hb : ∀ i, Within 61 (b i)) :
    Reduced (mulReduce a b) := by
  exact (reduce_bounds _ (by convert mul_bounds a b ha hb using 1)).1

theorem squareReduce_bounds (a : Felem) (ha : ∀ i, Within 61 (a i)) :
    Reduced (squareReduce a) := by
  exact (reduce_bounds _ (by convert square_bounds a ha using 1)).1

end P384
