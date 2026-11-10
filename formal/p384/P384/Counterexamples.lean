import P384.Machine

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option exponentiation.threshold 2048

namespace P384

def negCommentPre (a : Felem) : Prop :=
  ∀ i, 0 ≤ a i ∧ a i < 2^60 - 2^29

def negCounterexample : Felem := ![0, 2^60 - 2^52 - 2^4 + 1, 0, 0, 0, 0, 0]

theorem negCounterexample_admitted : negCommentPre negCounterexample := by
  unfold negCommentPre
  decide

theorem negCounterexample_underflows :
    machineNeg negCounterexample 1 = 2^64 - 1 := by decide

theorem negCounterexample_residue :
    (eval7 (machineNeg negCounterexample) + eval7 negCounterexample) % (p : ℤ) = 2^120 := by
  decide

theorem negCounterexample_incorrect :
    ¬ Congruent (eval7 (machineNeg negCounterexample)) (-eval7 negCounterexample) := by
  unfold Congruent
  decide

theorem neg_comment_pre_insufficient :
    ¬ (∀ a, negCommentPre a → Congruent (eval7 (machineNeg a)) (-eval7 a)) := by
  intro h
  exact negCounterexample_incorrect (h negCounterexample negCounterexample_admitted)

theorem neg_zero_output_exceeds_comment : machineNeg (fun _ => 0) 0 > 2^60 := by decide

theorem neg_comment_output_bound_false :
    ¬ (∀ a, negCommentPre a → ∀ i, machineNeg a i < 2^60) := by
  intro h
  have hz : negCommentPre (fun _ => 0) := by intro i; norm_num [negCommentPre]
  have hb := h _ hz 0
  have hc := neg_zero_output_exceeds_comment
  omega

end P384
