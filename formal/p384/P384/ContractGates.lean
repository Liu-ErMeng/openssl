import P384.ContractConditions

set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace P384

open Classical

noncomputable def wordFlag (p : Prop) : BitVec 64 := if p then BitVec.allOnes 64 else 0

theorem wordFlag_and (p q : Prop) : wordFlag p &&& wordFlag q = wordFlag (p ∧ q) := by
  by_cases hp : p <;> by_cases hq : q <;> simp [wordFlag, hp, hq]

theorem wordFlag_or (p q : Prop) : wordFlag p ||| wordFlag q = wordFlag (p ∨ q) := by
  by_cases hp : p <;> by_cases hq : q <;> simp [wordFlag, hp, hq]

theorem wordFlag_not (p : Prop) : ~~~wordFlag p = wordFlag (¬p) := by
  by_cases hp : p <;> simp [wordFlag, hp]

def contractMainGate (c : Fin 5 → BitVec 64) : BitVec 64 :=
  c 0 &&& (c 1 ||| (c 2 &&& (~~~c 3 ||| c 4)))

def contractBitGate (c : Fin 5 → BitVec 64) : BitVec 64 := c 0 &&& c 1

def contractOtherGate (c : Fin 5 → BitVec 64) : BitVec 64 :=
  (c 0 &&& ~~~c 1) &&& (c 2 &&& (~~~c 3 ||| c 4))

theorem contractMainGate_correct (a : LimbWords) (ha : serialFelem (fun i => unsigned (a i))) :
    contractMainGate (machineContractConditionsTrace a).conditions =
      wordFlag (contractNeedsSubtract (fun i => unsigned (a i))) := by
  have hc : (machineContractConditionsTrace a).conditions =
      fun i => wordFlag (contractPredicates (fun j => unsigned (a j)) i) :=
    machineContractConditions_correct a ha
  rw [hc]
  simp only [contractMainGate, wordFlag_and, wordFlag_or, wordFlag_not]
  rfl

theorem contractBitGate_correct (a : LimbWords) (ha : serialFelem (fun i => unsigned (a i))) :
    contractBitGate (machineContractConditionsTrace a).conditions =
      wordFlag (contractNeedsSubtract (fun i => unsigned (a i)) ∧
        contractPredicates (fun i => unsigned (a i)) 1) := by
  have hc : (machineContractConditionsTrace a).conditions =
      fun i => wordFlag (contractPredicates (fun j => unsigned (a j)) i) :=
    machineContractConditions_correct a ha
  rw [hc]
  simp only [contractBitGate, wordFlag_and]
  apply congrArg wordFlag
  apply propext
  unfold contractNeedsSubtract
  tauto

theorem contractOtherGate_correct (a : LimbWords) (ha : serialFelem (fun i => unsigned (a i))) :
    contractOtherGate (machineContractConditionsTrace a).conditions =
      wordFlag (contractNeedsSubtract (fun i => unsigned (a i)) ∧
        ¬contractPredicates (fun i => unsigned (a i)) 1) := by
  have hc : (machineContractConditionsTrace a).conditions =
      fun i => wordFlag (contractPredicates (fun j => unsigned (a j)) i) :=
    machineContractConditions_correct a ha
  rw [hc]
  simp only [contractOtherGate, wordFlag_and, wordFlag_or, wordFlag_not]
  apply congrArg wordFlag
  apply propext
  unfold contractNeedsSubtract
  tauto

end P384
