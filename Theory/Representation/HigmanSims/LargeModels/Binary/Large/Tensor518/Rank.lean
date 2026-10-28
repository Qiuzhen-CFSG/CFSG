module

public import Theory.Representation.HigmanSims.LargeModels.Binary.Large.Tensor518.Rank.Certificate
public import Theory.Representation.HigmanSims.LargeModels.Binary.Large.Tensor518.Assembly

/-!
# Full row rank of the degree-518 HS tensor section

The supplied 539-column minor of the 21 kernel rows followed by the 518
lifts has the supplied inverse. `Rank.Certificate` checks both the literal
minor interpretation and every row of the product using kernel reduction.
The existing pivot transport then gives the exact sum-index right inverse
and surjectivity needed by the tensor-section descent.

Source: R. A. Wilson et al., ATLAS HSG1-f2r518B0 and the saved tensor-section
certificate in `Binary/source/section518.json`. Attribution, retained rights
and reproducible generation are documented in `Rank/source/README.md`.
-/

public section
namespace Representation.HigmanSims.LargeModels.Binary.Large.Tensor518

/-- The literal saved pivot minor and inverse multiply to the identity. -/
theorem pivot_inverse : pivotMinor * pivotInverse = 1 := by
  rw [Rank.pivotMinor_eq]
  exact Rank.packed_product

/-- The exact right inverse on the sum of kernel and lift row indices. -/
theorem stacked_rightInverse :
    ∃ R : Matrix (Fin 1120) (Fin 21 ⊕ Fin 518) (ZMod 2),
      Descent.stackedRows kernelMatrix liftMatrix * R = 1 :=
  stacked_rightInverse_of_pivotInverse pivot_inverse

/-- Every coordinate vector is attained by a vector annihilated by the kernel
rows, discharging the rank premise of the marked tensor-section descent. -/
theorem rowSurjectivity :
    ∀ y : Fin 518 → ZMod 2, ∃ x,
      kernelMatrix.mulVec x = 0 ∧ liftMatrix.mulVec x = y :=
  rowSurjectivity_of_pivotInverse pivot_inverse

end Representation.HigmanSims.LargeModels.Binary.Large.Tensor518
