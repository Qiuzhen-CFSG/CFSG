module
public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSUThreeGeneration.OuterFamilies.FourActors.CentralizerGeometry.InvertedOddSubgroup.ActorCoordinates.Setup
import all CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSUThreeGeneration.InnerFamilies.Geometry.SemidihedralTorus.Model
/-!
# Exact action on the norm-one rotation curve

The sign formula and the stored field involution give a single Boolean
choice of identity or inversion for every norm-one parameter. This refines
the existing preservation theorem to the literal formula required by the
outer-actor coordinate interface.

The internal import continues the matrix calculation in `SemidihedralTorus.Model`;
its private matrix formulas remain private. No existing boundary is changed.
Source: Aschbacher--Smith E.1.14(7), printed p.214, citing Aschbacher (1982),
Lemma 4.11.
-/

public section
open Matrix Subgroup BenderSuzuki.MatrixGroups
open HermitianForm.EvenInner
namespace CFSG.Quasithin.ChapterE.ValuesOdd.PSUThreeGeneration.OuterFamilies.FourActors.CentralizerGeometry.InvertedOddSubgroup.AbelianGeometry
open InnerGeometry.SemidihedralTorus
variable {F : Type*} [Field F]
/-- The Boolean choice is uniform over the entire rotation curve. -/
theorem rotation_action_of_signSemilinear (J : HermitianForm 3 F)
    (hJ : J.form = 1) (h2 : (2 : F) ≠ 0)
    (a : MulAut (ProjectiveSpecialUnitaryMatrixGroup J)) (ha : HasSignSemilinearForm J a) :
    ∃ ε : Bool, ∀ k : normOne J,
      a (projectiveRotation J hJ h2 k) =
        projectiveRotation J hJ h2 (if ε then k⁻¹ else k) := by
  classical
  obtain ⟨s, σ, hσ, ha⟩ := ha
  have hsign (k : normOne J) :
      ProjGenLinGroup.mk (signGL s) * (projectiveRotation J hJ h2 k).val *
        (ProjGenLinGroup.mk (signGL s))⁻¹ =
          (projectiveRotation J hJ h2 (if s 0 = s 2 then k else k⁻¹)).val := by
    simp only [projectiveRotation_val]
    rw [← map_inv, ← map_mul, ← map_mul, sign_conjugates_rotation]
    split_ifs <;> rfl
  rcases hσ with rfl | rfl
  · refine ⟨decide (s 0 ≠ s 2), ?_⟩
    intro k
    apply Subtype.ext
    rw [ha]
    change ProjGenLinGroup.mk (signGL s) *
      ProjGenLinGroup.map (RingHom.id F) _ * (ProjGenLinGroup.mk (signGL s))⁻¹ = _
    rw [ProjGenLinGroup.map_id, MonoidHom.id_apply, hsign]
    simp only [decide_eq_true_eq, ite_not]
  · refine ⟨decide (s 0 = s 2), ?_⟩
    intro k
    apply Subtype.ext
    rw [ha]
    have hf : ProjGenLinGroup.map J.conj.toRingHom (projectiveRotation J hJ h2 k).val =
        (projectiveRotation J hJ h2 k⁻¹).val := by
      rw [projectiveRotation_val, projectiveRotation_val,
        ProjGenLinGroup.map_mk, conjugation_maps_rotation]
      rfl
    rw [hf, hsign]
    simp only [decide_eq_true_eq, inv_inv]
end CFSG.Quasithin.ChapterE.ValuesOdd.PSUThreeGeneration.OuterFamilies.FourActors.CentralizerGeometry.InvertedOddSubgroup.AbelianGeometry
