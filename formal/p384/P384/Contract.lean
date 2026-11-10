import P384.ContractFirst
import P384.ContractCarry
import P384.ContractSubtract
import P384.InterfaceValues

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 16384

namespace P384

theorem machineContractTail_decompose (a : LimbWords) :
    (machineContractTailTrace a).limbs =
      (machineContractCarryTrace (machineContractSubtractTrace a).limbs).limbs := by
  rfl

theorem machineContractTail_pack (a : Felem) (ha : serialFelem a) :
    (machineContractTailTrace (fun i => BitVec.ofInt 64 (a i))).limbs =
      fun i => BitVec.ofInt 64 (contractTail a i) := by
  rw [machineContractTail_decompose, contractSubtract_pack a ha,
    machineContractCarry_pack _ (contractSubtract_zero_bounds a ha) (contractSubtract_bounds a ha)]
  rfl

theorem machineContract_pack (a : Felem) (ha : Reduced a) :
    machineContract (fun i => BitVec.ofInt 64 (a i)) =
      fun i => BitVec.ofInt 64 (contractInteger a i) := by
  rw [machineContract, machineContractFirst_pack a ha,
    machineContractTail_pack _ (contractFirst_correct a ha).2]
  rfl

theorem machineContract_refines (a : LimbWords) (ha : Reduced (fun i => unsigned (a i))) :
    (fun i => unsigned (machineContract a i)) = contractInteger (fun i => unsigned (a i)) := by
  have he := machineContract_pack (fun i => unsigned (a i)) ha
  have hin : (fun i => BitVec.ofInt 64 (unsigned (a i))) = a := by
    funext i
    exact ofInt_unsigned _
  rw [hin] at he
  have hb := (contractInteger_correct _ ha).2
  funext i
  rw [congrFun he i]
  exact unsigned_ofInt_exact 64 _ (within_mono (serialFelem_limb_bound _ hb i) (by decide))

theorem machineContract_correct (a : LimbWords) (ha : Reduced (fun i => unsigned (a i))) :
    eval7 (fun i => unsigned (machineContract a i)) = eval7 (fun i => unsigned (a i)) % (p : ℤ) ∧
      serialFelem (fun i => unsigned (machineContract a i)) := by
  rw [machineContract_refines a ha]
  exact contractInteger_correct _ ha

theorem serialFelem_reduced (a : Felem) (ha : serialFelem a) : Reduced a :=
  ⟨ha.1, ha.2.1, le_of_lt ha.2.2⟩

theorem machineContract_range (a : LimbWords) (ha : Reduced (fun i => unsigned (a i))) :
    0 ≤ eval7 (fun i => unsigned (machineContract a i)) ∧
      eval7 (fun i => unsigned (machineContract a i)) < (p : ℤ) := by
  rw [(machineContract_correct a ha).1]
  have hp : (0 : ℤ) < p := by exact_mod_cast p_pos
  exact ⟨Int.emod_nonneg _ (ne_of_gt hp), Int.emod_lt_of_pos _ hp⟩

theorem machineContract_idempotent (a : LimbWords) (ha : Reduced (fun i => unsigned (a i))) :
    machineContract (machineContract a) = machineContract a := by
  have h1 := machineContract_correct a ha
  have h2 := machineContract_correct (machineContract a) (serialFelem_reduced _ h1.2)
  have hv : eval7 (fun i => unsigned (machineContract (machineContract a) i)) =
      eval7 (fun i => unsigned (machineContract a i)) := by
    rw [h2.1, h1.1, Int.emod_emod]
  have he := eval7_injective _ _ (serialFelem_limb_bound _ h2.2) (serialFelem_limb_bound _ h1.2) hv
  funext i
  exact eq_of_unsigned_eq (congrFun he i)

theorem machineContract_to_bn_value (mem : ByteMemory) (off : ℕ) (a : LimbWords)
    (ha : Reduced (fun i => unsigned (a i))) :
    (bnWordValue (bnImportLE (readMemory (serializeMemory mem off (machineContract a)) off 48)) : ℤ) =
      eval7 (fun i => unsigned (a i)) % (p : ℤ) := by
  rw [felem_memory_to_bn_value mem off _ (machineContract_correct a ha).2,
    (machineContract_correct a ha).1]

end P384
