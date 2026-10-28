module

public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degree320Pair.NativeActions.MatrixRelations.GeneratorOrders
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degree320Pair.NativeActions.MatrixRelations.RemainingGeneratorOrders
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degree320Pair.NativeActions.MatrixRelations.ProductOrder23
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degree320Pair.NativeActions.MatrixRelations.CommutatorOrders
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degree320Pair.NativeActions.MatrixRelations.MixedRelators

/-!
# Assembly of the seven degree-320 ATLAS row relations

Kernel-checked finite arithmetic proves the generator equations and all five
longer positive relators for both literal matrix pairs. `matrixRelations`
assembles these certificates with no additional hypotheses, supplying the exact
matrix premise of `NativeActions.actionsExist_of_relations`. The existing
conditional assembly remains available with its original interface.

Source: John Bray's ATLAS presentation M24G1-P1. The source inverse elimination
and transpose conversion are proved in the shared `Presentation` module;
this calculation uses only the original, untransposed matrices.
-/

@[expose] public section
namespace Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degree320Pair
open MatrixRelationCertificate

/-- Discharge the certified 320a square clause and assemble the remaining clauses. -/
theorem matrixRelations_of_remaining
    (hA : matrixA true ^ 2 = 1)
    (hB : ∀ v, matrixB v ^ 3 = 1)
    (h23 : ∀ v, (matrixA v * matrixB v) ^ 23 = 1)
    (h12 : ∀ v, (matrixA v * matrixB v ^ 2 * matrixA v * matrixB v) ^ 12 = 1)
    (h5 : ∀ v, (matrixA v * matrixB v ^ 2 * matrixA v * matrixB v ^ 2 *
      matrixA v * matrixB v * matrixA v * matrixB v) ^ 5 = 1)
    (hCubes : ∀ v, (matrixA v * matrixB v * matrixA v * matrixB v *
      matrixA v * matrixB v ^ 2) ^ 3 *
      (matrixA v * matrixB v * matrixA v * matrixB v ^ 2 *
        matrixA v * matrixB v ^ 2) ^ 3 = 1)
    (h4 : ∀ v, (matrixA v * matrixB v *
      (matrixA v * matrixB v * matrixA v * matrixB v ^ 2) ^ 3) ^ 4 = 1) :
    MatrixRelations := by
  intro v i
  fin_cases i
  · cases v
    · exact square_matrixA_false
    · exact hA
  · exact hB v
  · exact h23 v
  · exact h12 v
  · exact h5 v
  · exact hCubes v
  · exact h4 v

/-- All seven positive ATLAS row relations for both literal degree-320 pairs.
False selects 320a and true selects 320b; the matrices are untransposed. -/
theorem matrixRelations : MatrixRelations :=
  matrixRelations_of_remaining square_matrixA_true cube_matrixB product_order23
    commutator_order12 second_commutator_order5 mixed_cubes last_order4

end Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degree320Pair
