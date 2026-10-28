/-
Copyright (c) 2026 Gerald Höhn and the ATLAS contributors. All rights reserved.
Adapted from ATLAS, revision 8eabb35afe2b5e45bf913a2d05c53e558d2e2917.
Covered by the ATLAS Research and Attribution License 1.0 (LICENSES/ATLAS.txt).
Changes: Lean 4.33 modules, narrow imports, and CFSG quadratic-isometry carriers.
-/
module

public import Theory.SpecificGroups.ClassicalOrthogonal.RankOneComparison.Image
public import Theory.SpecificGroups.ClassicalOrthogonal.RankOneComparison.Kernel

/-! # Actual B₁/A₁ comparison in every characteristic

Conjugation on trace-zero matrices has the scalar SL₂ center as kernel and
exactly the actual elementary orthogonal group as image. Its scalar isometries
are trivial, so the same comparison identifies the actual projective model.
No finite-field order comparison or source perfectness is used.

Adapted from ATLAS `LinearGroups/Orthogonal/B1ConjugationComparison.lean`.
The comparison uses the literal carriers in GLS3 §2.7 and is applied to
the quotient recognition step of Aschbacher–Smith B.1.13.
-/
@[expose] public noncomputable section
namespace ClassicalOrthogonal.RankOneComparison
variable {F : Type*} [Field F]

def toElementary : SL (F := F) →* elementarySubgroup (formB 1 F) :=
  toOrthogonal.codRestrict _ toOrthogonal_mem_elementary

theorem toElementary_surjective : Function.Surjective (toElementary (F := F)) := by
  intro g
  have hg : g.val ∈ (toOrthogonal (F := F)).range := by rw [toOrthogonal_range]; exact g.prop
  obtain ⟨a,ha⟩ := hg
  exact ⟨a,Subtype.ext ha⟩

theorem toElementary_kernel : (toElementary (F := F)).ker = Subgroup.center (SL (F := F)) := by
  ext g
  change toElementary g = 1 ↔ _
  rw [← toOrthogonal_eq_one_iff_center]
  exact ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩

/-- The actual elementary rank-one B group, without projectivization, is already PSL₂. -/
def elementaryEquivPSL : elementarySubgroup (formB 1 F) ≃*
    Matrix.ProjectiveSpecialLinearGroup (Fin 2) F :=
  (QuotientGroup.quotientKerEquivOfSurjective (toElementary (F := F)) toElementary_surjective).symm.trans
    (QuotientGroup.quotientMulEquivOfEq (toElementary_kernel (F := F)))

/-- There are no nonidentity scalar isometries in the actual elementary B₁ group. -/
theorem elementaryScalar_eq_bot : elementaryScalarSubgroup (formB 1 F) = ⊥ := by
  apply bot_unique
  rintro g ⟨c,hc,hg⟩
  obtain ⟨a,rfl⟩ := toElementary_surjective g
  have ha := (scalar_action_implies_center a c hg).2
  change toElementary a = 1
  apply Subtype.ext
  exact toOrthogonal_eq_one_of_center a ha

/-- Actual B₁/A₁ comparison over every field, including the rank-one exceptional fields. -/
def projectiveEquivPSL : ProjectiveElementary (formB 1 F) ≃*
    Matrix.ProjectiveSpecialLinearGroup (Fin 2) F :=
  ((QuotientGroup.quotientMulEquivOfEq (elementaryScalar_eq_bot (F := F))).trans
    QuotientGroup.quotientBot).trans elementaryEquivPSL

/-- The comparison agrees with the original SL₂ conjugation action on each lift. -/
theorem elementaryEquivPSL_projection (g : SL (F := F)) :
    elementaryEquivPSL (toElementary g) = QuotientGroup.mk g := by
  let e := QuotientGroup.quotientKerEquivOfSurjective (toElementary (F := F)) toElementary_surjective
  change (QuotientGroup.quotientMulEquivOfEq (toElementary_kernel (F := F)))
    (e.symm (e (QuotientGroup.mk g))) = _
  rw [MulEquiv.symm_apply_apply]
  rfl

theorem projectiveEquivPSL_projection (g : SL (F := F)) :
    projectiveEquivPSL (projectiveElementaryMap _ (toElementary g)) = QuotientGroup.mk g :=
  elementaryEquivPSL_projection g

end ClassicalOrthogonal.RankOneComparison
