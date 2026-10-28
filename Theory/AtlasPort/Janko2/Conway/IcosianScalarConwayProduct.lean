/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Conway/IcosianScalarConwayProduct.lean.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
Source revision: 8eabb35afe2b5e45bf913a2d05c53e558d2e2917.
-/
module

public import Theory.AtlasPort.Janko2.Conway.IcosianScalarIntersection
public import Theory.AtlasPort.Janko2.Algebra.IcosianScalarProjective

/-!
# IcosianScalarConwayProduct

The scalar and linear sign quotients have commuting, disjoint images in the
Leech central quotient. Exact preimage and intersection calculations prove that their product map is injective.

Source: Gerald Höhn, `Atlas/Conway/IcosianScalarConwayProduct.lean`, ATLAS revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted to CFSG Lean 4.33.0 with public imports and the definition bodies
needed by the source coordinate calculations; source statements are preserved.
-/

set_option backward.isDefEq.respectTransparency false
@[expose] public section

noncomputable section
namespace Atlas.Conway
open Atlas.Algebra Atlas.Lattices

theorem icosianScalarSigns_eq_comap :
    icosianNormOneReduction.ker=leechCentralSigns.comap icosianScalarsToCo0 := by
  ext u
  rw [icosianNormOneReduction_kernel_iff]
  change (u=1 ∨ u=icosianNormOneMinusOne) ↔ icosianScalarsToCo0 u∈leechCentralSigns
  rw [leechCentralSigns_mem]
  constructor
  · rintro (rfl|rfl)
    · exact Or.inl (map_one _)
    · exact Or.inr icosianScalarsToCo0_minusOne
  · rintro (h|h)
    · left
      apply icosianScalarsToCo0_injective
      simpa only [map_one] using h
    · right
      exact icosianScalarsToCo0_injective (h.trans icosianScalarsToCo0_minusOne.symm)

def icosianScalarProjectiveToCo1 : IcosianScalarProjectiveModel →* LeechCentralQuotient :=
  QuotientGroup.map _ _ icosianScalarsToCo0 (le_of_eq icosianScalarSigns_eq_comap)

theorem icosianScalarProjectiveToCo1_injective :
    Function.Injective icosianScalarProjectiveToCo1 := by
  apply (MonoidHom.ker_eq_bot_iff icosianScalarProjectiveToCo1).mp
  rw [icosianScalarProjectiveToCo1,QuotientGroup.ker_map,← icosianScalarSigns_eq_comap]
  exact QuotientGroup.map_mk'_self _

theorem icosianScalarProjectiveToCo1_range :
    icosianScalarProjectiveToCo1.range=icosianScalarsToCo0.range.map leechCentralProjection := by
  ext z
  constructor
  · rintro ⟨u,rfl⟩
    obtain ⟨v,rfl⟩ := QuotientGroup.mk'_surjective icosianNormOneReduction.ker u
    exact ⟨icosianScalarsToCo0 v,⟨v,rfl⟩,rfl⟩
  · rintro ⟨_,⟨v,rfl⟩,rfl⟩
    exact ⟨QuotientGroup.mk v,rfl⟩

theorem icosianProjectiveToCo1_range :
    icosianProjectiveToCo1.range=icosianCentralizer.map leechCentralProjection := by
  ext z
  constructor
  · rintro ⟨g,rfl⟩
    obtain ⟨f,rfl⟩ := QuotientGroup.mk'_surjective icosianCentralSigns g
    exact ⟨icosianHermitianToCo0 f,icosianHermitianToCo0_mem f,rfl⟩
  · rintro ⟨x,hx,rfl⟩
    obtain ⟨f,hf⟩ := icosianHermitianToCo0_surjective_centralizer ⟨x,hx⟩
    exact ⟨QuotientGroup.mk f,congrArg leechCentralProjection hf⟩

theorem icosianScalarProjective_commute (u : IcosianScalarProjectiveModel)
    (g : IcosianProjectiveModel) :
    Commute (icosianScalarProjectiveToCo1 u) (icosianProjectiveToCo1 g) := by
  obtain ⟨v,rfl⟩ := QuotientGroup.mk'_surjective icosianNormOneReduction.ker u
  obtain ⟨f,rfl⟩ := QuotientGroup.mk'_surjective icosianCentralSigns g
  exact (icosianScalars_commute_Hermitian v f).map leechCentralProjection

theorem icosianScalarProjective_ranges_disjoint :
    Disjoint icosianScalarProjectiveToCo1.range icosianProjectiveToCo1.range := by
  rw [disjoint_iff,icosianScalarProjectiveToCo1_range,icosianProjectiveToCo1_range]
  apply Subgroup.comap_injective leechCentralProjection_surjective
  have hu : leechCentralProjection.ker ≤ icosianScalarsToCo0.range := by
    rw [leechCentralProjection_kernel,← icosianScalars_inf_centralizer]
    exact inf_le_left
  have hc : leechCentralProjection.ker ≤ icosianCentralizer := by
    rw [leechCentralProjection_kernel,← icosianScalars_inf_centralizer]
    exact inf_le_right
  rw [Subgroup.comap_inf,Subgroup.comap_map_eq_self hu,Subgroup.comap_map_eq_self hc,
    MonoidHom.comap_bot,leechCentralProjection_kernel]
  exact icosianScalars_inf_centralizer

/-- The scalar sign quotient and actual quaternionic projective group embed
as a direct product in the retained Conway central quotient. -/
def icosianScalarProjectiveProductToCo1 :
    IcosianScalarProjectiveModel × IcosianProjectiveModel →* LeechCentralQuotient :=
  icosianScalarProjectiveToCo1.noncommCoprod icosianProjectiveToCo1 icosianScalarProjective_commute

theorem icosianScalarProjectiveProductToCo1_injective :
    Function.Injective icosianScalarProjectiveProductToCo1 :=
  (MonoidHom.noncommCoprod_injective _ _ _).mpr
    ⟨icosianScalarProjectiveToCo1_injective,icosianProjectiveToCo1_injective,
      icosianScalarProjective_ranges_disjoint⟩

end Atlas.Conway
