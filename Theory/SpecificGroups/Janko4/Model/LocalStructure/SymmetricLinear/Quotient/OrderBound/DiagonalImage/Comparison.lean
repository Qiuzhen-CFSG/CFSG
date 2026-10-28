module

public import Theory.SpecificGroups.Janko4.Model.LocalStructure.SymmetricLinear.Quotient.OrderBound.DiagonalImage.Data
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.SymmetricLinear.Quotient.OrderBound.Filtration

/-! The packed factorization targets are exactly the simultaneous diagonal
blocks of the certified ATLAS coordinates. A row mask checks all fifteen
blocks; no selected-factor faithfulness is assumed. See source/README.md. -/

public section
namespace Janko4.LocalStructure.SymmetricLinear.OrderBound.DiagonalFactors

private theorem blockIndex_lt (i : Fin 112) : blockIndex i < 15 := by
  revert i
  decide +kernel

private def blockOf (i : Fin 112) : Fin 15 := ⟨blockIndex i, blockIndex_lt i⟩

set_option maxRecDepth 10000 in
private theorem blockMasks_bits (b : Fin 15) (j : Fin 112) :
    (blockMasks.get b).testBit j.val = decide (b.val = blockIndex j) := by
  revert j
  fin_cases b <;> decide +kernel

private theorem decode_diagonal_of_mask (xs ys : Vector ℕ 112)
    (h : ∀ i, ys.get i = xs.get i &&& blockMasks.get (blockOf i)) :
    decodeRows ys = Matrix.blockDiagonalPart blockIndex (decodeRows xs) := by
  funext i j
  simp only [decodeRows, h, Nat.testBit_and, blockMasks_bits, Matrix.blockDiagonalPart]
  change (if (xs.get i).testBit j.val && decide (blockIndex i = blockIndex j) then 1 else 0) = _
  by_cases hij : blockIndex i = blockIndex j <;> simp [hij]

theorem decode_diagonalFirstRows : decodeRows diagonalFirstRows =
    Matrix.blockDiagonalPart blockIndex (decodeRows firstRows) := by
  apply decode_diagonal_of_mask
  decide +kernel

theorem decode_diagonalSecondRows : decodeRows diagonalSecondRows =
    Matrix.blockDiagonalPart blockIndex (decodeRows secondRows) := by
  apply decode_diagonal_of_mask
  decide +kernel

end Janko4.LocalStructure.SymmetricLinear.OrderBound.DiagonalFactors
