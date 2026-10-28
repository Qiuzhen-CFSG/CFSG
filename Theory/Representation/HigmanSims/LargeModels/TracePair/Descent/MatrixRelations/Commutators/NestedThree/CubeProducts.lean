module

public import Theory.Representation.HigmanSims.LargeModels.TracePair.Descent.MatrixRelations.Commutators.NestedThree.Inner
public import Theory.Representation.HigmanSims.LargeModels.TracePair.Descent.MatrixRelations.Commutators.NestedThree.InnerSquare
public import Theory.Representation.HigmanSims.LargeModels.TracePair.Descent.MatrixRelations.Commutators.NestedThree.InnerCube

/-!
# Complete formation and cube products for the nested HS candidate

The three public products check every coordinate of the fixed literal matrices.
Each uses bounded kernel-checked row certificates and the proved streaming
interpretation as matrix multiplication over `Four`. No group-word, action,
invertibility, shared-gate or mixed-square premise is used.

Source: the retained HSG1-f4r896aB0 matrices, with attribution and conventions
in `TracePair/source/README.md`. These products discharge three premises of
the reduction for `(x,y*x*y)^3` in `Descent/source/HSG1-P1.M`.
`InnerCube/Application` supplies that importing application with the shared
circuit and mixed squares explicit. See `InnerCube/source/README.md` for
reproduction and measurements.
-/
