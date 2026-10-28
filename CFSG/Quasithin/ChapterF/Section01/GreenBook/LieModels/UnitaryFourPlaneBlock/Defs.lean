module

public import Theory.SpecificGroups.ClassicalUnitary.UnitaryFourPlaneLocal
public import CFSG.Quasithin.ChapterF.Section01.GreenBook.LieModels.UnitaryFour

/-!
# The second local factor in the unitary-four amalgam

The factor L₂ is defined by determinant one on the invariant coordinate plane,
inside the concrete plane parabolic. The injective canonical map SU₄ → PSU₄
identifies its matrix and projective realizations. Normality is relative to
the plane parabolic in both realizations.

Source: Aschbacher--Smith F.1.12(I)(6), printed pp.263–264. The radical,
quotient, shortness and literal Ω₄⁻ natural-module identification of C.1.30
(printed p.135) are not yet asserted by this initial construction.
-/

@[expose] public noncomputable section
namespace CFSG.Quasithin.ChapterF.GreenBook.LieModels.UnitaryFour

open Theory.SpecificGroups.ClassicalUnitary.UnitaryFourFlag
open Theory.SpecificGroups.ClassicalUnitary.UnitaryFourPlaneLocal

variable (n : ℕ) (hn : 1 ≤ n)

/-- The determinant-one plane factor inside the actual special unitary group. -/
def L2Matrix : Subgroup (MatrixGroup n hn) :=
  localFactor (MatrixField n) (standardForm n hn)

/-- Its image under the same projective map used by the flag amalgam. -/
def L2 : Subgroup (ProjectiveGroup n hn) := (L2Matrix n hn).map (projection n hn)

theorem L2Matrix_le_planeParabolic : L2Matrix n hn ≤ planeParabolicMatrix n hn :=
  local_le_planeParabolic (MatrixField n) (standardForm n hn)

theorem L2_le_planeParabolic : L2 n hn ≤ planeParabolic n hn :=
  Subgroup.map_mono (L2Matrix_le_planeParabolic n hn)

instance L2Matrix_normal_in_plane :
    ((L2Matrix n hn).subgroupOf (planeParabolicMatrix n hn)).Normal :=
  local_normal_in_plane (MatrixField n) (standardForm n hn)

instance L2_normal_in_plane : ((L2 n hn).subgroupOf (planeParabolic n hn)).Normal := by
  apply (Subgroup.normal_subgroupOf_iff_le_normalizer (L2_le_planeParabolic n hn)).mpr
  exact (Subgroup.map_mono (Subgroup.le_normalizer_of_normal_subgroupOf
    (L2Matrix_le_planeParabolic n hn))).trans
      ((L2Matrix n hn).le_normalizer_map (projection n hn))

/-- No abstract family identification: this is the restriction of projectivization. -/
def L2ProjectIso : L2Matrix n hn ≃* L2 n hn :=
  Subgroup.equivMapOfInjective _ _ (projection_injective n hn)

/-- The concrete restriction map to determinant-one two-by-two matrices. -/
def L2MatrixRestriction : L2Matrix n hn →*
    Matrix.SpecialLinearGroup (Fin 2) (MatrixField n) :=
  factorRestriction (MatrixField n) (standardForm n hn)

/-- Restriction transported along the proved projective isomorphism. -/
def L2Restriction : L2 n hn →* Matrix.SpecialLinearGroup (Fin 2) (MatrixField n) :=
  (L2MatrixRestriction n hn).comp (L2ProjectIso n hn).symm.toMonoidHom

@[simp] theorem L2Restriction_project (g : L2Matrix n hn) :
    L2Restriction n hn (L2ProjectIso n hn g) = L2MatrixRestriction n hn g := by
  simp [L2Restriction]

/-- Every matrix two-subgroup in the plane parabolic is contained in L₂. -/
theorem two_subgroup_le_L2Matrix (S : Subgroup (MatrixGroup n hn))
    (hS : IsPGroup 2 S) (hSP : S ≤ planeParabolicMatrix n hn) : S ≤ L2Matrix n hn :=
  two_subgroup_le_localFactor (MatrixField n) (standardForm n hn) S hS hSP

/-- In particular the plane factor contains each Sylow two-subgroup of its parabolic. -/
theorem two_subgroup_le_L2 (S : Subgroup (ProjectiveGroup n hn))
    (hS : IsPGroup 2 S) (hSP : S ≤ planeParabolic n hn) : S ≤ L2 n hn := by
  have hP : (planeParabolic n hn).comap (projection n hn) = planeParabolicMatrix n hn := by
    change Subgroup.comap _ (Subgroup.map _ _) = _
    apply Subgroup.comap_map_eq_self
    rw [(projection n hn).ker_eq_bot_iff.mpr (projection_injective n hn)]
    exact bot_le
  have hle := two_subgroup_le_L2Matrix n hn (S.comap (projection n hn))
    (hS.comap_of_injective (projection n hn) (projection_injective n hn))
    (by simpa only [hP] using Subgroup.comap_mono (f := projection n hn) hSP)
  intro x hx
  obtain ⟨a,rfl⟩ := project_surjective (MatrixField n) (standardForm n hn) x
  exact ⟨a, hle hx, rfl⟩

end CFSG.Quasithin.ChapterF.GreenBook.LieModels.UnitaryFour
