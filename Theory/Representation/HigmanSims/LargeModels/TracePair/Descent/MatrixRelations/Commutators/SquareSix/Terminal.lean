module

public import Theory.Representation.HigmanSims.LargeModels.TracePair.Descent.MatrixRelations.Commutators.SquareSix.Terminal.Cube0
public import Theory.Representation.HigmanSims.LargeModels.TracePair.Descent.MatrixRelations.Commutators.SquareSix.Terminal.Cube1
public import Theory.Representation.HigmanSims.LargeModels.TracePair.Descent.MatrixRelations.Commutators.SquareSix.Terminal.Cube2
public import Theory.Representation.HigmanSims.LargeModels.TracePair.Descent.MatrixRelations.Commutators.SquareSix.Terminal.Cube3
public import Theory.Representation.HigmanSims.LargeModels.TracePair.Descent.MatrixRelations.Commutators.SquareSix.Terminal.Inverse0
public import Theory.Representation.HigmanSims.LargeModels.TracePair.Descent.MatrixRelations.Commutators.SquareSix.Terminal.Inverse1
public import Theory.Representation.HigmanSims.LargeModels.TracePair.Descent.MatrixRelations.Commutators.SquareSix.Terminal.Inverse2
public import Theory.Representation.HigmanSims.LargeModels.TracePair.Descent.MatrixRelations.Commutators.SquareSix.Terminal.Inverse3
public import Theory.Representation.HigmanSims.LargeModels.TracePair.Descent.MatrixRelations.Commutators.SquareSix.Sample

/-!
# The two terminal products of the squared-generator HS commutator

For the published candidate matrices C, D and E, the kernel certificates prove
D C = E and E² = I over Four, in the original dimension and basis. Joining
consecutive checked ranges covers every row and `productCheck_of_range`
transports those numerical checks to the literal matrix products.

The last sixteen rows of E² reuse `terminal_tail_checked`. No interpretation
of C, D or E as powers is assumed. `Terminal/Application.lean` connects these
products to the sixth-power relation, with only the common and initial products
left explicit. Source: HSG1-P1.M, (a,b²)⁶, and the retained ATLAS matrices.
-/

public section
namespace Representation.HigmanSims.LargeModels.TracePair.Descent.MatrixRelations.Commutators.SquareSix
open Certificates.OrbitSpans.RowChecks Terminal

private theorem cube_checked : CheckedRange (rowCheck 2) 0 896 :=
  checkedRange_append _ 0 448 448
    (checkedRange_append _ 0 224 224 cube0_checked cube1_checked)
    (checkedRange_append _ 448 224 224 cube2_checked cube3_checked)

private theorem inverse_checked : CheckedRange (rowCheck 3) 0 896 :=
  checkedRange_append _ 0 448 448
    (checkedRange_append _ 0 224 224 inverse0_checked inverse1_checked)
    (checkedRange_append _ 448 224 224 inverse2_checked
      (checkedRange_append _ 672 208 16 inverse3_checked terminal_tail_checked))

/-- The exact last two fixed products, with all rows and columns certified. -/
theorem terminal_products : ProductCheck 2 ∧ ProductCheck 3 :=
  ⟨productCheck_of_range 2 cube_checked, productCheck_of_range 3 inverse_checked⟩

end Representation.HigmanSims.LargeModels.TracePair.Descent.MatrixRelations.Commutators.SquareSix
