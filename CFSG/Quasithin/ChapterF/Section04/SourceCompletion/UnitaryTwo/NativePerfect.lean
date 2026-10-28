module

public import CFSG.Quasithin.ChapterF.Section01.GreenBook.LieModels.UnitaryFour.BinaryOrders
public import Theory.SpecificGroups.ClassicalUnitary.UnitaryFourPointResidual.AmbientPerfectness

/-!
# Perfectness of the native binary unitary completion

The established antidiagonal SU₄ root-group generation theorem makes the
actual stored matrix group perfect, including the smallest field. Its
canonical projective image is therefore perfect. This is the model input
for the automorphism-image comparison in the U₄(2) case of F.4.24.
-/

@[expose] public noncomputable section
namespace CFSG.Quasithin.ChapterF.SourceCompletion.UnitaryTwo
open GreenBook.LieModels.UnitaryFour
open Theory.SpecificGroups.ClassicalUnitary
local notation "h1" => (Nat.le_refl 1)

theorem native_matrix_perfect : Group.IsPerfect (MatrixGroup 1 h1) := by
  apply UnitaryFourPointResidual.AmbientPerfectness.antidiagonal_isPerfect
  change ∃ x : GaloisField 2 (1 * 2),
    iterateFrobeniusEquiv (GaloisField 2 (1 * 2)) 2 1 x ≠ x
  exact GaloisField.BinaryQuadratic.conj_nontrivial 1 (by decide)

theorem native_projective_perfect : Group.IsPerfect (ProjectiveGroup 1 h1) := by
  have := native_matrix_perfect
  exact Group.IsPerfect.ofSurjective (f := projection 1 h1) (UnitaryFourFlag.project_surjective _ _)

end CFSG.Quasithin.ChapterF.SourceCompletion.UnitaryTwo
