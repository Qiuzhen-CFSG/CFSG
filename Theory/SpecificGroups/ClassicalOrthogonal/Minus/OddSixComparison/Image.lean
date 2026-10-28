module

public import Theory.SpecificGroups.ClassicalOrthogonal.Minus.OddSixComparison.FieldModel
public import Theory.SpecificGroups.ClassicalOrthogonal.Minus.OddSixComparison.SignedCoordinates
public import Theory.SpecificGroups.ClassicalOrthogonal.Minus.OddSixComparison.Quotient
public import Theory.SpecificGroups.ClassicalOrthogonal.Minus.OddSixComparison.Image.Root
public import Theory.SpecificGroups.ClassicalOrthogonal.Minus.OddSixComparison.Image.Containment
public import Theory.SpecificGroups.ClassicalOrthogonal.Minus.OddSixComparison.Image.SingularLines
public import Mathlib.GroupTheory.IsPerfect

/-!
# Projective image of the minus-six exterior action

The geometric image argument is made on the original full isometry group:
concrete Siegel lifts put its elementary subgroup in the exterior image.
The elementary subgroup is ambient normal and contains an explicit nonscalar
root. Its image through the original commutator's scalar quotient therefore
exhausts that quotient, using only inherited projective simplicity.

Perfectness of the actual odd special unitary source supplies commutator
containment, including at fixed-field order three. `Image.Containment` proves
this through signed unitary elimination. `Image.Root` and `Image.SingularLines`
prove the first-direction lifts and their transport to all singular lines.
This module discharges every image premise and applies the exact scalar-kernel
comparison, retaining only the geometric realization, its signed coordinates,
odd characteristic and inherited projective simplicity. No separate cardinality
hypothesis is needed for this implication from the given realization.

The resulting projective equivalence supplies the minus-six identification
used to reduce the small orthogonal cases in A.2.17. Construction of the
geometric realization remains with the parent comparison assembly.

Source: GLS3 §2.7 and Aschbacher–Smith A.2.17, printed pp.38–39.
-/

public noncomputable section
namespace ClassicalOrthogonal.Minus.OddSixComparison
open BenderSuzuki.MatrixGroups

variable {F E : Type} [Field F] [Finite F] [Field E]
variable {J : HermitianForm 4 E} (R : ExteriorRealization F E J)

/-- Perfectness of the actual source puts its exterior action in the
commutator of the original full isometry group. -/
theorem ExteriorRealization.action_mem_commutator_of_perfect
    [Group.IsPerfect J.specialSubgroup] (g : J.specialSubgroup) :
    R.action g ∈ commutator (FullOrthogonal F) := by
  have hm := map_derivedSeries_le_derivedSeries R.action 1
  rw [derivedSeries_one, derivedSeries_one, Group.IsPerfect.commutator_eq_top] at hm
  exact hm ⟨g, Subgroup.mem_top _, rfl⟩

variable (hlift : ∀ (u v : Space F 2) (hu : quadraticForm F 3 u = 0)
  (huv : (quadraticForm F 3).polarBilin u v = 0),
  siegelElement (quadraticForm F 3) u v hu huv ∈ R.action.range)

include hlift in
/-- Actual lifts put the whole elementary subgroup inside the exterior image. -/
theorem ExteriorRealization.elementary_le_range_of_siegel :
    elementarySubgroup (quadraticForm F 3) ≤ R.action.range := by
  apply (Subgroup.closure_le _).mpr
  rintro _ ⟨u, v, hu, huv, rfl⟩
  exact hlift u v hu huv

variable (hcomm : ∀ g, R.action g ∈ commutator (FullOrthogonal F))

include hlift in
/-- Lifting is compatible with precisely the published projective exterior map. -/
theorem ExteriorRealization.projectiveElementary_le_range_of_siegel :
    Image.projectiveElementary F ≤ (R.projectiveAction hcomm).range := by
  rintro x ⟨z, hz, rfl⟩
  obtain ⟨g, hg⟩ := R.elementary_le_range_of_siegel hlift hz
  refine ⟨g, ?_⟩
  rw [ExteriorRealization.projectiveAction_apply]
  apply congrArg (QuotientGroup.mk' _)
  apply Subtype.ext
  simpa only [ExteriorRealization.omegaAction_val, Subgroup.subtype_apply] using hg

include hlift in
/-- Projective simplicity and concrete Siegel lifts exhaust the original
projective carrier, without asserting simplicity of its central cover. -/
theorem ExteriorRealization.projectiveAction_surjective_of_siegel
    [IsSimpleGroup (ClassicalGroup.POmegaMinus 3 F)] :
    Function.Surjective (R.projectiveAction hcomm) := by
  have hRO : R.action.range ≤ commutator (FullOrthogonal F) := by
    rintro _ ⟨g, rfl⟩
    exact hcomm g
  have hE := Image.projectiveElementary_eq_top F
    ((R.elementary_le_range_of_siegel hlift).trans hRO)
  have hER := R.projectiveElementary_le_range_of_siegel hlift hcomm
  rw [hE] at hER
  exact MonoidHom.range_eq_top.mp (top_unique hER)

include hlift in
/-- The normality conclusion lives in the actual projective carrier. -/
theorem ExteriorRealization.projectiveAction_normal_of_siegel
    [IsSimpleGroup (ClassicalGroup.POmegaMinus 3 F)] :
    (R.projectiveAction hcomm).range.Normal := by
  rw [MonoidHom.range_eq_top.mpr (R.projectiveAction_surjective_of_siegel hlift hcomm)]
  infer_instance

/-- Literal application of the two-scalar-kernel quotient comparison. -/
def ExteriorRealization.projectiveEquiv_of_siegel
    [IsSimpleGroup (ClassicalGroup.POmegaMinus 3 F)] :
    ClassicalGroup.POmegaMinus 3 F ≃* ProjectiveSpecialUnitaryMatrixGroup J :=
  R.projectiveEquiv_of_surjective hcomm
    (R.projectiveAction_surjective_of_siegel hlift hcomm)

/-- The equivalence keeps the original SU-to-PSU projection on representatives. -/
@[simp] theorem ExteriorRealization.projectiveEquiv_of_siegel_apply
    [IsSimpleGroup (ClassicalGroup.POmegaMinus 3 F)] (g : J.specialSubgroup) :
    R.projectiveEquiv_of_siegel hlift hcomm (R.projectiveAction hcomm g) =
      Theory.SpecificGroups.ClassicalUnitary.UnitaryFourFlag.project E J g :=
  R.projectiveEquiv_of_surjective_apply _ _ _

include hlift in
/-- Assembly of the two independent image inputs. Odd perfectness and all-line
Siegel lifting must still be supplied before this yields the source image theorem. -/
theorem ExteriorRealization.exists_commutator_normal_of_perfect_of_siegel
    [Group.IsPerfect J.specialSubgroup]
    [IsSimpleGroup (ClassicalGroup.POmegaMinus 3 F)] :
    ∃ hcomm : ∀ g, R.action g ∈ commutator (FullOrthogonal F),
      (R.projectiveAction hcomm).range.Normal :=
  ⟨R.action_mem_commutator_of_perfect,
    R.projectiveAction_normal_of_siegel hlift R.action_mem_commutator_of_perfect⟩

section Signed
variable {p n : ℕ} [Fact p.Prime] [NeZero n]
variable (R : ExteriorRealization F (Extension p n) (unitaryForm p n))
variable (C : SignedCoordinates R)

include C in
/-- The signed first-direction calculation discharges local lifting. Only
perfectness and transport of nonzero singular vectors remain as image inputs. -/
theorem ExteriorRealization.exists_commutator_normal_of_perfect_of_transport
    [Group.IsPerfect (unitaryForm p n).specialSubgroup]
    [IsSimpleGroup (ClassicalGroup.POmegaMinus 3 F)]
    (htrans : ∀ (u : Space F 2), quadraticForm F 3 u = 0 → u ≠ 0 →
      ∃ (g : (unitaryForm p n).specialSubgroup) (b : F), b ≠ 0 ∧
        (R.action g).val u = b • Image.direction F) :
    ∃ hcomm : ∀ g, R.action g ∈ commutator (FullOrthogonal F),
      (R.projectiveAction hcomm).range.Normal :=
  R.exists_commutator_normal_of_perfect_of_siegel
    (R.siegel_mem_range_of_direction_and_transport
      (Image.direction_siegel_mem_range R C) htrans)

variable [IsSimpleGroup (ClassicalGroup.POmegaMinus 3 F)]

include C in
/-- The actual signed odd exterior action surjects onto the original projective
orthogonal carrier. Commutator containment and every Siegel lift are proved,
including at fixed-field order three. -/
theorem ExteriorRealization.projectiveAction_surjective (hp : p ≠ 2) :
    Function.Surjective (R.projectiveAction (R.action_mem_commutator hp)) :=
  R.projectiveAction_surjective_of_siegel (Image.siegel_mem_range R C)
    (R.action_mem_commutator hp)

include C in
/-- Normality holds in the original commutator's scalar quotient. Only that
projective carrier is assumed simple. -/
theorem ExteriorRealization.projectiveAction_normal (hp : p ≠ 2) :
    (R.projectiveAction (R.action_mem_commutator hp)).range.Normal := by
  rw [MonoidHom.range_eq_top.mpr (R.projectiveAction_surjective C hp)]
  infer_instance

include C in
/-- The complete image input for the odd minus-six comparison: no additional
perfectness, generation, transport, lifting or normality premise remains. -/
theorem ExteriorRealization.exists_commutator_normal (hp : p ≠ 2) :
    ∃ hcomm : ∀ g, R.action g ∈ commutator (FullOrthogonal F),
      (R.projectiveAction hcomm).range.Normal :=
  ⟨R.action_mem_commutator hp, R.projectiveAction_normal C hp⟩

/-- Applying the exact scalar-kernel theorem to the proved image identifies
the literal projective carriers from the supplied signed realization. -/
def ExteriorRealization.projectiveEquiv_of_signedCoordinates (hp : p ≠ 2) :
    ClassicalGroup.POmegaMinus 3 F ≃*
      ProjectiveSpecialUnitaryMatrixGroup (unitaryForm p n) :=
  R.projectiveEquiv_of_surjective (R.action_mem_commutator hp)
    (R.projectiveAction_surjective C hp)

/-- The equivalence sends the original exterior class of each SU₄ element to
its original SU₄-to-PSU₄ class. -/
@[simp] theorem ExteriorRealization.projectiveEquiv_of_signedCoordinates_apply
    (hp : p ≠ 2) (g : (unitaryForm p n).specialSubgroup) :
    R.projectiveEquiv_of_signedCoordinates C hp
        (R.projectiveAction (R.action_mem_commutator hp) g) =
      Theory.SpecificGroups.ClassicalUnitary.UnitaryFourFlag.project
        (Extension p n) (unitaryForm p n) g :=
  R.projectiveEquiv_of_surjective_apply _ _ _

end Signed

end ClassicalOrthogonal.Minus.OddSixComparison
