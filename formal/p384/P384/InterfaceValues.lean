import P384.BNImport
import P384.BNExport
import P384.SerializationMemory

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option exponentiation.threshold 1024

namespace P384

def bnWordBytes (ws : List (BitVec 64)) : List Byte := ws.flatMap (fun w => encodeLE 8 w.toNat)

@[simp] theorem bnWordBytes_length (ws : List (BitVec 64)) :
    (bnWordBytes ws).length = 8 * ws.length := by
  induction ws with
  | nil => rfl
  | cons w ws ih => simp [bnWordBytes] at ih ⊢; omega

theorem bnWordBytes_value (ws : List (BitVec 64)) :
    leValue (bnWordBytes ws) = bnWordValue ws := by
  induction ws with
  | nil => rfl
  | cons w ws ih =>
      simp only [bnWordBytes, List.flatMap_cons, leValue_append, encodeLE_length,
        leValue_encodeLE, bnWordValue]
      rw [Nat.mod_eq_of_lt (show w.toNat < 256^8 from w.isLt)]
      change w.toNat + 2^64 * leValue (bnWordBytes ws) = _
      rw [ih]

theorem bnWordBytes_take (ws : List (BitVec 64)) (top : ℕ) :
    (bnWordBytes ws).take (8 * top) = bnWordBytes (ws.take top) := by
  induction top generalizing ws with
  | zero => simp [bnWordBytes]
  | succ top ih =>
      cases ws with
      | nil => simp [bnWordBytes]
      | cons w ws =>
          simp only [bnWordBytes, List.flatMap_cons, List.take_succ_cons]
          have hp : 8 * (top + 1) = (encodeLE 8 w.toNat).length + 8 * top := by simp; omega
          rw [hp, List.take_append]
          exact congrArg (fun rest => encodeLE 8 w.toNat ++ rest) (ih ws)

theorem bn_word_export_felem_value (ws : List (BitVec 64)) (top : ℕ)
    (ht : top ≤ ws.length) (hc : 8 * ws.length < 2^63)
    (hv : bnWordValue (ws.take top) < 2^384) :
    eval7 (fun i => unsigned (bin48ToFelem (bnExportLE (bnWordBytes ws) (8 * top) 48) i)) =
      bnWordValue (ws.take top) := by
  have hb := bnExportLE48_to_felem (bnWordBytes ws) (8 * top)
    (by simp; omega) (by simpa using hc)
    (by simpa only [bnWordBytes_take, bnWordBytes_value] using hv)
  simpa only [bnWordBytes_take, bnWordBytes_value] using hb

theorem bn_import_export48_value (ws : List (BitVec 64)) (top : ℕ)
    (ht : top ≤ ws.length) (hc : 8 * ws.length < 2^63)
    (hv : bnWordValue (ws.take top) < 2^384) :
    bnWordValue (bnImportLE (bnExportLE (bnWordBytes ws) (8 * top) 48)) =
      bnWordValue (ws.take top) := by
  rw [bnImportLE_value, bnExportLE_value _ _ _ (by simp; omega) (by simpa using hc)
    (by norm_num), bnWordBytes_take, bnWordBytes_value]
  exact Nat.mod_eq_of_lt hv

theorem felem_memory_to_bn_value (mem : ByteMemory) (off : ℕ) (a : Fin 7 → BitVec 64)
    (ha : serialFelem (fun i => unsigned (a i))) :
    (bnWordValue (bnImportLE (readMemory (serializeMemory mem off a) off 48)) : ℤ) =
      eval7 (fun i => unsigned (a i)) := by
  rw [bnImportLE_value, serializeMemory_value mem off a ha]

end P384
