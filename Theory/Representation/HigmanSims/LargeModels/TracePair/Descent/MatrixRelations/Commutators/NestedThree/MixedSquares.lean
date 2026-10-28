module

public import Theory.Representation.HigmanSims.LargeModels.TracePair.Descent.MatrixRelations.Commutators.NestedThree.ABFourthSquare
public import Theory.Representation.HigmanSims.LargeModels.TracePair.Descent.MatrixRelations.Commutators.NestedThree.ABSquare

/-!
# The two mixed squares in the nested HS commutator

The two producers check all 896 rows of the literal products `AB4 * AB4`
and `AB * AB`. Each proof joins 56 independently checked intervals of 16
coordinates and applies the streaming multiplier's matrix semantics over `Four`.

These equalities discharge the two square premises of
`nested_commutator_three_of_shared_products`. The interpretation of the inputs
as `A B⁴` and `A B` belongs to the shared-gate producer; the three subsequent
products and the final unconditional relator remain with their assembly owner.

Source: the unchanged ATLAS HSG1-f4r896aB0 matrices retained in
`TracePair/source/`, and relator 5 of `Descent/source/HSG1-P1.M`.
Reproduction and measurements are recorded in `ABSquare/source/README.md`.
-/
