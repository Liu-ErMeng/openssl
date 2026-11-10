import P384.Contract
import P384.MachineInversion

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option exponentiation.threshold 2048

namespace P384

def canonicalBNWords (mem : ByteMemory) (off : ℕ) (a : LimbWords) : List (BitVec 64) :=
  bnImportLE (readMemory (serializeMemory mem off (machineContract a)) off 48)

theorem canonicalBNWords_value (mem : ByteMemory) (off : ℕ) (a : LimbWords)
    (ha : Reduced (fun i => unsigned (a i))) :
    (bnWordValue (canonicalBNWords mem off a) : ℤ) = eval7 (fun i => unsigned (a i)) % (p : ℤ) :=
  machineContract_to_bn_value mem off a ha

theorem machineMul_to_bn_value (mem : ByteMemory) (off : ℕ) (a b : LimbWords)
    (ha : ∀ i, unsigned (a i) < 2^61) (hb : ∀ i, unsigned (b i) < 2^61) :
    (bnWordValue (canonicalBNWords mem off (machineMulReduce a b)) : ℤ) =
      (eval7 (fun i => unsigned (a i)) * eval7 (fun i => unsigned (b i))) % (p : ℤ) := by
  have hm := machineMulReduce_correct a b ha hb
  rw [canonicalBNWords_value mem off _ hm.2]
  exact hm.1

theorem machineSquare_to_bn_value (mem : ByteMemory) (off : ℕ) (a : LimbWords)
    (ha : ∀ i, unsigned (a i) < 2^61) :
    (bnWordValue (canonicalBNWords mem off (machineSquareReduce a)) : ℤ) =
      eval7 (fun i => unsigned (a i))^2 % (p : ℤ) := by
  have hs := machineSquareReduce_correct a ha
  rw [canonicalBNWords_value mem off _ hs.2]
  exact hs.1

theorem canonicalBNWords_field (mem : ByteMemory) (off : ℕ) (a : LimbWords)
    (ha : Reduced (fun i => unsigned (a i))) :
    (bnWordValue (canonicalBNWords mem off a) : ZMod p) = wordField a := by
  change ((bnWordValue (canonicalBNWords mem off a) : ℤ) : ZMod p) =
    ((eval7 (fun i => unsigned (a i))) : ZMod p)
  apply (ZMod.intCast_eq_intCast_iff' _ _ p).2
  rw [canonicalBNWords_value mem off a ha, Int.emod_emod]

theorem machineInv_to_bn_inverse (mem : ByteMemory) (off : ℕ) (a : LimbWords)
    (ha : Reduced (fun i => unsigned (a i))) (hn : wordField a ≠ 0) :
    wordField a * (bnWordValue (canonicalBNWords mem off (machineInv a)) : ZMod p) = 1 := by
  have hi := machineInv_correct a ha hn
  rw [canonicalBNWords_field mem off _ hi.2]
  exact hi.1

end P384
