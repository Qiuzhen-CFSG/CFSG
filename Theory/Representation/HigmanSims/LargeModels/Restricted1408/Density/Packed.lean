module

public import Theory.LinearAlgebra.PackedBinaryRows
public import Theory.SpecificGroups.Thompson.Model.GeneratorCertificates.BinaryMatrix

public import Theory.Representation.HigmanSims.LargeModels.Restricted1408.Density.Witnesses

/-!
# Packed row checks on the literal restriction matrices

The existing list-based XOR computation agrees with the Thompson binary
matrix decoder. The two application lemmas retain the literal HS matrix
rows and their row-action convention. No external arithmetic is trusted.
-/

public section
namespace PackedBinaryRows
open Thompson.BinaryMatrix

lemma rowRange_zero_eq_rowProduct (x : ℕ) (rows : Array ℕ) (n : ℕ) :
    rowRange x (fun i => rows[i]!) 0 n = rowProduct x rows n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [rowRange, rowProduct, Nat.zero_add, ih]

lemma rowProduct_eq_listProduct (x : ℕ) (rows : Array ℕ) (n : ℕ)
    (hlen : rows.size = n) :
    rowProduct x rows n = listProduct x 0 rows.toList := by
  rw [← rowRange_zero_eq_rowProduct]
  apply rowRange_eq_blockProduct x (fun i => rows[i]!) 0 n rows hlen
  intro i
  simp only [Nat.zero_add]

/-- A packed row computation certifies ordinary row action on the decoded matrix. -/
theorem vecMul_decode_of_listProduct (n : ℕ) (rows : Array ℕ) (x y : ℕ)
    (hlen : rows.size = n) (h : listProduct x 0 rows.toList = y) :
    Matrix.vecMul (fun i : Fin n => bit x i.val) (decode n rows) =
      fun i : Fin n => bit y i.val := by
  funext j
  change (∑ k : Fin n, bit x k.val * bit rows[k.val]! j.val) = bit y j.val
  rw [Fin.sum_univ_eq_sum_range (fun k => bit x k * bit rows[k]! j.val),
    ← bit_rowProduct, rowProduct_eq_listProduct x rows n hlen, h]
end PackedBinaryRows

namespace Representation.HigmanSims.LargeModels.Restricted1408.Density

theorem aRows_size : aRows.size = 1408 := by decide +kernel

theorem bRows_size : bRows.size = 1408 := by decide +kernel

theorem vecMul_matrixA_of_listProduct (x y : ℕ)
    (h : PackedBinaryRows.listProduct x 0 aRows.toList = y) :
    Matrix.vecMul (vectorOfBits x) matrixA = vectorOfBits y :=
  PackedBinaryRows.vecMul_decode_of_listProduct 1408 aRows x y aRows_size h

theorem vecMul_matrixB_of_listProduct (x y : ℕ)
    (h : PackedBinaryRows.listProduct x 0 bRows.toList = y) :
    Matrix.vecMul (vectorOfBits x) matrixB = vectorOfBits y :=
  PackedBinaryRows.vecMul_decode_of_listProduct 1408 bRows x y bRows_size h

theorem vectorOfBits_xor (x y : ℕ) :
    vectorOfBits (x ^^^ y) = vectorOfBits x + vectorOfBits y := by
  funext i
  exact Thompson.BinaryMatrix.bit_xor x y i.val

theorem vectorOfBits_zero : vectorOfBits 0 = 0 := by
  funext i
  simp [vectorOfBits, Thompson.BinaryMatrix.bit]

end Representation.HigmanSims.LargeModels.Restricted1408.Density
