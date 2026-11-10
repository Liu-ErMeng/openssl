import P384.BNToFelem
import P384.FieldInterfaces

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option exponentiation.threshold 2048

namespace P384

theorem bnToFelemCall_limb_bound (s : BN64State) (hs : BN64Valid s)
    (out : LimbWords) (mem : ByteMemory) (off : ℕ)
    (hret : (bnToFelemCall s out mem off).status = 1) :
    ∀ i, unsigned ((bnToFelemCall s out mem off).limbs i) < 2^61 := by
  have hv := bnToFelemCall_checked s hs out mem off hret
  intro i
  have hi := serialFelem_limb_bound _ hv.2 i
  exact (within_mono hi (by decide : 56 ≤ 61)).2

theorem checkedBNMul_value (a b : BN64State) (ha : BN64Valid a) (hb : BN64Valid b)
    (oldA oldB : LimbWords) (memA memB memOut : ByteMemory) (offA offB offOut : ℕ)
    (hretA : (bnToFelemCall a oldA memA offA).status = 1)
    (hretB : (bnToFelemCall b oldB memB offB).status = 1) :
    (bnWordValue (canonicalBNWords memOut offOut
      (machineMulReduce (bnToFelemCall a oldA memA offA).limbs
        (bnToFelemCall b oldB memB offB).limbs)) : ℤ) =
      ((bnMagnitude a : ℤ) * bnMagnitude b) % (p : ℤ) := by
  have hvalA := (bnToFelemCall_checked a ha oldA memA offA hretA).1
  have hvalB := (bnToFelemCall_checked b hb oldB memB offB hretB).1
  rw [machineMul_to_bn_value memOut offOut _ _
    (bnToFelemCall_limb_bound a ha oldA memA offA hretA)
    (bnToFelemCall_limb_bound b hb oldB memB offB hretB), hvalA, hvalB]

theorem checkedBNSquare_value (a : BN64State) (ha : BN64Valid a)
    (old : LimbWords) (memIn memOut : ByteMemory) (offIn offOut : ℕ)
    (hret : (bnToFelemCall a old memIn offIn).status = 1) :
    (bnWordValue (canonicalBNWords memOut offOut
      (machineSquareReduce (bnToFelemCall a old memIn offIn).limbs)) : ℤ) =
      (bnMagnitude a : ℤ)^2 % (p : ℤ) := by
  rw [machineSquare_to_bn_value memOut offOut _ (bnToFelemCall_limb_bound a ha old memIn offIn hret),
    (bnToFelemCall_checked a ha old memIn offIn hret).1]

theorem checkedBNInv_inverse (a : BN64State) (ha : BN64Valid a)
    (old : LimbWords) (memIn memOut : ByteMemory) (offIn offOut : ℕ)
    (hret : (bnToFelemCall a old memIn offIn).status = 1) (hn : (bnMagnitude a : ZMod p) ≠ 0) :
    (bnMagnitude a : ZMod p) *
      (bnWordValue (canonicalBNWords memOut offOut (machineInv (bnToFelemCall a old memIn offIn).limbs)) : ZMod p) = 1 := by
  have hv := bnToFelemCall_checked a ha old memIn offIn hret
  have he : wordField (bnToFelemCall a old memIn offIn).limbs = (bnMagnitude a : ZMod p) := by
    unfold wordField fieldValue
    rw [hv.1]
    rfl
  have hi := machineInv_to_bn_inverse memOut offOut _ (serialFelem_reduced _ hv.2) (by rw [he]; exact hn)
  rwa [he] at hi

end P384
