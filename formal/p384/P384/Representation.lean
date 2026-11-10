import P384.WordSemantics

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace P384

def radixList : List ℤ → ℤ
  | [] => 0
  | x :: xs => x + radix * radixList xs

theorem radixList_injective (xs ys : List ℤ)
    (hx : ∀ x ∈ xs, Within 56 x) (hy : ∀ y ∈ ys, Within 56 y)
    (hlen : xs.length = ys.length) (hv : radixList xs = radixList ys) : xs = ys := by
  induction xs generalizing ys with
  | nil => cases ys with
      | nil => rfl
      | cons y ys => simp at hlen
  | cons x xs ih =>
      cases ys with
      | nil => simp at hlen
      | cons y ys =>
          have hxn := hx x (by simp)
          have hyn := hy y (by simp)
          have hmod := congrArg (fun n => n % radix) hv
          have hxmod : x % radix = x := Int.emod_eq_of_lt hxn.1 hxn.2
          have hymod : y % radix = y := Int.emod_eq_of_lt hyn.1 hyn.2
          simp only [radixList, Int.add_emod, Int.mul_emod, Int.emod_self, zero_mul,
            Int.zero_emod, add_zero, Int.emod_emod, hxmod, hymod] at hmod
          have htail : radixList xs = radixList ys := by
            simp only [radixList] at hv
            rw [hmod] at hv
            norm_num [radix] at hv
            omega
          have he := ih ys (fun z hz => hx z (by simp [hz]))
            (fun z hz => hy z (by simp [hz])) (by simpa using hlen) htail
          rw [hmod, he]

def limbList (a : Felem) : List ℤ := [a 0, a 1, a 2, a 3, a 4, a 5, a 6]

theorem radixList_eval7 (a : Felem) : radixList (limbList a) = eval7 a := by
  simp only [radixList, limbList, eval7]
  ring

theorem limbList_bounds (a : Felem) (ha : ∀ i, Within 56 (a i)) :
    ∀ x ∈ limbList a, Within 56 x := by
  have h : (limbList a).Forall (Within 56) := ⟨ha 0, ha 1, ha 2, ha 3, ha 4, ha 5, ha 6⟩
  exact List.forall_iff_forall_mem.1 h

theorem eval7_injective (a b : Felem) (ha : ∀ i, Within 56 (a i)) (hb : ∀ i, Within 56 (b i))
    (hv : eval7 a = eval7 b) : a = b := by
  have hl : limbList a = limbList b := radixList_injective _ _ (limbList_bounds a ha)
    (limbList_bounds b hb) rfl (by simpa only [radixList_eval7] using hv)
  funext i
  have hi := congrArg (fun xs : List ℤ => xs[i.val]!) hl
  fin_cases i <;> simpa [limbList] using hi

end P384
