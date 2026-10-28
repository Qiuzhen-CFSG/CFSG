module

public import Theory.SpecificGroups.ClassicalUnitary.FiveFourRadicalCentralizers.Reduction
public import Theory.SpecificGroups.ClassicalUnitary.FiveFourRadicalCentralizers.LineMatrices
public import Theory.SpecificGroups.ClassicalUnitary.FiveFourRadicalCentralizers.PlaneMatrices

/-!
# The radical-centralizer calculation for PSU₅(4)

The reduction module proves coprime lifting of projective commutation, derives
a trace-one element from the actual Frobenius data, and normalizes the two
matrix shapes into the existing radical embeddings. The independent line and
plane commutant calculations discharge both matrix-shape premises. Thus the
centralizer of each concrete unipotent subgroup in its full projective
parabolic is contained in that subgroup.

These bounds use only the field, Frobenius and identity-form hypotheses;
normality and identification with the parabolic two-core are separate results.

Source: Aschbacher--Smith, Theorem 0.1.2(1) and F.1.12(7), printed pp.4 and
263--264 of `refs/quasithin.pdf`.
-/

public section

open BenderSuzuki.MatrixGroups
namespace Theory.SpecificGroups.UnitaryFive.RadicalCentralizers

variable {F : Type*} [Field F] [Finite F] [CharP F 2]
variable (J : HermitianForm 5 F)

/-- The centralizer of the concrete line unipotent subgroup in the full
projective line parabolic is contained in that unipotent subgroup. -/
theorem line_centralizer_le (hJ : J.form = 1)
    (hconj : ∀ x : F, J.conj x = x ^ 4) (hcard : Nat.card F = 16) :
    Subgroup.centralizer
        (LineCore.Parabolic.projectiveUnipotent J hJ : Set (lineParabolic J)) ≤
      LineCore.Parabolic.projectiveUnipotent J hJ :=
  line_centralizer_le_of_matrix_shape J hJ hconj hcard (line_matrix_shape J)

/-- The centralizer of the concrete plane unipotent subgroup in the full
projective plane parabolic is contained in that unipotent subgroup. -/
theorem plane_centralizer_le (hJ : J.form = 1)
    (hconj : ∀ x : F, J.conj x = x ^ 4) (hcard : Nat.card F = 16) :
    Subgroup.centralizer
        (PlaneCore.projectiveUnipotent J hJ : Set (planeParabolic J)) ≤
      PlaneCore.projectiveUnipotent J hJ :=
  plane_centralizer_le_of_matrix_shape J hJ hconj hcard (plane_commutant_normal_form J)

end Theory.SpecificGroups.UnitaryFive.RadicalCentralizers
