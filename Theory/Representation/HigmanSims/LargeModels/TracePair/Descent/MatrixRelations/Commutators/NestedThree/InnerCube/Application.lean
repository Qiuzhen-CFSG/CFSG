module

public import Theory.Representation.HigmanSims.LargeModels.TracePair.Descent.MatrixRelations.Commutators.NestedThree.CubeProducts
public import Theory.Representation.HigmanSims.LargeModels.TracePair.Descent.MatrixRelations.Commutators.NestedThree

/-!
# Applying the three checked cube products

The complete literal products discharge the formation, square, and cube
premises of the nested-commutator reduction. The shared circuit and the two
mixed squares remain explicit for the source-relator assembly owner.

Source: `(x,y*x*y)^3` in `Descent/source/HSG1-P1.M`; matrix data and
conventions are recorded in `TracePair/source/README.md`.
-/

public section
namespace Representation.HigmanSims.LargeModels.TracePair.Descent.MatrixRelations
open Certificates Commutators.NestedThree

/-- Only the independent shared circuit and mixed squares remain. -/
theorem nested_commutator_three_of_shared_and_mixed_squares
    (hshared : ∀ i : Fin 46, i.val < 17 → LongWords.ProductCheck i)
    (hX2 : Packed.eval 896 rowsAB4 * Packed.eval 896 rowsAB4 = Packed.eval 896 rowsAB4Sq)
    (hY2 : Packed.eval 896 rowsAB * Packed.eval 896 rowsAB = Packed.eval 896 rowsABSq) :
    positiveRelation (Packed.eval 896 generatorRowsA) (Packed.eval 896 generatorRowsB) 5 = 1 :=
  nested_commutator_three_of_shared_products hshared hX2 hY2
    inner_product inner_square inner_cube

end Representation.HigmanSims.LargeModels.TracePair.Descent.MatrixRelations
