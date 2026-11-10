import P384.ProductRefinement
import P384.Inversion
import P384.Prime

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000
set_option exponentiation.threshold 2048

namespace P384

def wordField (a : LimbWords) : ZMod p := fieldValue (fun i => unsigned (a i))
abbrev ReducedWords := { a : LimbWords // Reduced (fun i => unsigned (a i)) }

theorem reduced_word_bound (a : ReducedWords) : ∀ i, unsigned (a.val i) < 2^61 :=
  fun i => (reduced_within61 _ a.property i).2

def reducedWordSquare (a : ReducedWords) : ReducedWords :=
  ⟨machineSquareReduce a.val, (machineSquareReduce_correct _ (reduced_word_bound a)).2⟩

def reducedWordMul (a b : ReducedWords) : ReducedWords :=
  ⟨machineMulReduce a.val b.val,
    (machineMulReduce_correct _ _ (reduced_word_bound a) (reduced_word_bound b)).2⟩

theorem machineMulReduce_field (a b : LimbWords)
    (ha : ∀ i, unsigned (a i) < 2^61) (hb : ∀ i, unsigned (b i) < 2^61) :
    wordField (machineMulReduce a b) = wordField a * wordField b := by
  have h := (ZMod.intCast_eq_intCast_iff' _ _ p).2 (machineMulReduce_correct a b ha hb).1
  simpa only [wordField, fieldValue, Int.cast_mul] using h

theorem machineSquareReduce_field (a : LimbWords) (ha : ∀ i, unsigned (a i) < 2^61) :
    wordField (machineSquareReduce a) = wordField a * wordField a := by
  have h := (ZMod.intCast_eq_intCast_iff' _ _ p).2 (machineSquareReduce_correct a ha).1
  simpa only [wordField, fieldValue, Int.cast_pow, pow_two, Int.cast_mul] using h

def machineInv (a : LimbWords) : LimbWords := invProgram machineSquareReduce machineMulReduce a
def reducedWordInv (a : ReducedWords) : ReducedWords := invProgram reducedWordSquare reducedWordMul a

theorem reducedWordInv_val (a : ReducedWords) : (reducedWordInv a).val = machineInv a.val :=
  invProgram_map (fun x : ReducedWords => x.val) reducedWordSquare reducedWordMul
    machineSquareReduce machineMulReduce (fun _ => rfl) (fun _ _ => rfl) a

theorem machineInv_reduced (a : LimbWords) (ha : Reduced (fun i => unsigned (a i))) :
    Reduced (fun i => unsigned (machineInv a i)) := by
  have hv := reducedWordInv_val ⟨a, ha⟩
  rw [← hv]
  exact (reducedWordInv ⟨a, ha⟩).property

theorem machineInv_field (a : LimbWords) (ha : Reduced (fun i => unsigned (a i))) :
    wordField (machineInv a) = invChain (wordField a) := by
  let x : ReducedWords := ⟨a, ha⟩
  have hv := reducedWordInv_val x
  have hs : ∀ y : ReducedWords, wordField (reducedWordSquare y).val = wordField y.val * wordField y.val :=
    fun y => machineSquareReduce_field y.val (reduced_word_bound y)
  have hm : ∀ y z : ReducedWords,
      wordField (reducedWordMul y z).val = wordField y.val * wordField z.val :=
    fun y z => machineMulReduce_field y.val z.val (reduced_word_bound y) (reduced_word_bound z)
  have hf := invProgram_map (fun y : ReducedWords => wordField y.val)
    reducedWordSquare reducedWordMul (fun y => y * y) (fun y z => y * z) hs hm x
  change wordField (reducedWordInv x).val = invChain (wordField a) at hf
  rw [hv] at hf
  exact hf

theorem machineInv_exponent (a : LimbWords) (ha : Reduced (fun i => unsigned (a i))) :
    wordField (machineInv a) = wordField a ^ (p - 2) := by
  rw [machineInv_field a ha, invChain_exponent]

theorem machineInv_correct (a : LimbWords)
    (ha : Reduced (fun i => unsigned (a i))) (hn : wordField a ≠ 0) :
    wordField a * wordField (machineInv a) = 1 ∧
      Reduced (fun i => unsigned (machineInv a i)) := by
  refine ⟨?_, machineInv_reduced a ha⟩
  letI : Fact p.Prime := ⟨p_prime⟩
  rw [machineInv_exponent a ha, ← pow_succ']
  have he : p - 2 + 1 = p - 1 := by have := p_gt_two; omega
  rw [he]
  exact ZMod.pow_card_sub_one_eq_one hn

theorem machineInv_zero (a : LimbWords) (ha : Reduced (fun i => unsigned (a i)))
    (hn : wordField a = 0) : wordField (machineInv a) = 0 := by
  rw [machineInv_exponent a ha, hn]
  exact zero_pow (by have := p_gt_two; omega)

theorem invLimbs_correct_closed (a : Felem) (ha : fieldValue a ≠ 0) :
    fieldValue a * fieldValue (invLimbs a) = 1 := invLimbs_correct p_prime a ha

end P384
