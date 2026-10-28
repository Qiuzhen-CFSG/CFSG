module

public import Theory.SpecificGroups.Janko4.Model.GeneratorCertificates.Packed

/-!
# Row arithmetic for the Sylow matrix realization

Balanced natural-number lookup avoids repeatedly reducing literal vectors.
The scan is proved equal to the existing packed multiplication algorithm,
so its kernel-checked certificates imply ordinary binary matrix equations.

Source: the row convention of `GeneratorCertificates.Packed` and the literal
ATLAS matrices documented in `Model.Data`.
-/

@[expose] public section
namespace Janko4.LocalStructure.SylowNormalEights.MatrixRealization
open GeneratorCertificates

def scan (x : ℕ) (f : ℕ → ℕ) : ℕ → ℕ → ℕ
  | 0, _ => 0
  | count + 1, offset =>
    (if x.testBit offset then f offset else 0) ^^^ scan x f count (offset + 1)

theorem scan_eq (x : ℕ) (f : ℕ → ℕ) (count offset : ℕ) :
    scan x f count offset = xorList (List.ofFn (fun i : Fin count =>
      if x.testBit (offset + i.val) then f (offset + i.val) else 0)) := by
  induction count generalizing offset with
  | zero => rfl
  | succ count ih =>
    rw [scan, List.ofFn_succ, xorList, ih]
    simp only [Fin.val_zero, Nat.add_zero, Fin.val_succ,
      Nat.add_left_comm, Nat.add_comm]
    rfl

def rowsMatrix (a : ℕ → ℕ) : BinaryMatrix :=
  fun i j => bit (a i.val) j.val

theorem decode_ofFn (a : ℕ → ℕ) :
    decodeRows (Vector.ofFn (fun i : Fin 112 => a i.val)) = rowsMatrix a := by
  funext i j
  simp only [decodeRows, get_ofFn, rowsMatrix, bit]

theorem matrix_product (a b c : ℕ → ℕ)
    (h : ∀ i : Fin 112, scan (a i.val) b 112 0 = c i.val) :
    rowsMatrix a * rowsMatrix b = rowsMatrix c := by
  rw [← decode_ofFn a, ← decode_ofFn b, ← decode_ofFn c, ← decode_packedMul]
  apply congrArg decodeRows
  apply packedMul_eq_of_rows
  intro i
  simpa only [get_ofFn, packedRow, scan_eq, Nat.zero_add] using h i

theorem matrix_eq_decoded (a : ℕ → ℕ) (v : Vector ℕ 112)
    (h : ∀ i : Fin 112, a i.val = v.get i) : rowsMatrix a = decodeRows v := by
  funext i j
  change bit (a i.val) j.val = bit (v.get i) j.val
  rw [h]

def oneRows (n : ℕ) : ℕ := 2 ^ n

theorem matrix_one : rowsMatrix oneRows = 1 := by
  rw [← decode_ofFn]
  exact decode_packedOne

end Janko4.LocalStructure.SylowNormalEights.MatrixRealization
