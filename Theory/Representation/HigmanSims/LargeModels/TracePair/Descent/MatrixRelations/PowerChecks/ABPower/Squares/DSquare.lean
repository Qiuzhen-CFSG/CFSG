module

public import Theory.Representation.HigmanSims.LargeModels.TracePair.Descent.MatrixRelations.PowerChecks.ABPower.Squares.DLow
public import Theory.Representation.HigmanSims.LargeModels.TracePair.Descent.MatrixRelations.PowerChecks.ABPower.Squares.DHigh

/-!
# The fixed numerical square DD = E

The two bounded row families certify every row of the literal product.
`eval_product` identifies the resulting matrices over the unchanged `Four`.
Splitting the row checks bounds compilation memory; neither batch assumes
any earlier power identity. This is the second squaring link for relator 2
of `Descent/source/HSG1-P1.M`. See `Squares/source/README.md`.
-/

public section
namespace Representation.HigmanSims.LargeModels.TracePair.Descent.MatrixRelations.PowerChecks.ABPower.Squares
open Certificates LinearCertificates

/-- The square of the literal D matrix is the literal E matrix. -/
theorem d_square_eq_e : Packed.eval 896 dRows * Packed.eval 896 dRows =
    Packed.eval 896 eRows := by
  apply eval_product
  intro i
  by_cases h : i.val < 560
  · exact d_square_rows_low i.val (Nat.zero_le _) h
  · exact d_square_rows_high i.val (Nat.le_of_not_gt h) i.isLt

end Representation.HigmanSims.LargeModels.TracePair.Descent.MatrixRelations.PowerChecks.ABPower.Squares
