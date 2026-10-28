/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Conway/IcosianConwayEmbedding.lean.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
Source revision: 8eabb35afe2b5e45bf913a2d05c53e558d2e2917.
-/
module

public import Theory.AtlasPort.Janko2.Conway.IcosianProjectiveModel
public import Theory.AtlasPort.OtherSporadic.Conway.LeechCentralQuotient

/-!
# IcosianConwayEmbedding

The quaternionic central sign maps to Leech negation. The exact preimage of the
Leech signs therefore gives an injective map of the projective icosian group into the Leech central quotient.

Source: Gerald Höhn, `Atlas/Conway/IcosianConwayEmbedding.lean`, ATLAS revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted to CFSG Lean 4.33.0 with public imports and the definition bodies
needed by the source coordinate calculations; source statements are preserved.
-/

set_option backward.isDefEq.respectTransparency false
@[expose] public section

noncomputable section
namespace Atlas.Conway
open Atlas.Algebra Atlas.Lattices

/-- The transported quaternionic central sign is the retained Leech negation. -/
theorem icosianHermitianToCo0_sign :
    icosianHermitianToCo0 icosianCentralSign=negationIsometry := by
  have he := rationalExtension_unique negationIsometry.val
    (-LinearMap.id : RationalCoordinates →ₗ[ℚ] RationalCoordinates) (by
      intro x; rw [negationIsometry_apply]; simp)
  apply fullIsometryEquiv.injective
  apply Subtype.ext
  apply LinearEquiv.ext
  intro x
  rw [icosianHermitianToCo0_extension]
  change icosianComparison (icosianCentralSign.val (icosianComparison.symm x))=
    rationalExtension negationIsometry.val x
  rw [icosianCentralSign_apply,map_neg,LinearEquiv.apply_symm_apply]
  exact LinearMap.congr_fun he x

theorem icosianCentralSigns_eq_comap :
    icosianCentralSigns=leechCentralSigns.comap icosianHermitianToCo0 := by
  ext g
  change (g=1 ∨ g=icosianCentralSign) ↔ icosianHermitianToCo0 g∈leechCentralSigns
  rw [leechCentralSigns_mem]
  constructor
  · rintro (rfl|rfl)
    · exact Or.inl (map_one _)
    · exact Or.inr icosianHermitianToCo0_sign
  · rintro (h|h)
    · left
      apply icosianHermitianToCo0_injective
      simpa only [map_one] using h
    · right
      exact icosianHermitianToCo0_injective (h.trans icosianHermitianToCo0_sign.symm)

/-- The actual quaternionic projective group embeds in the retained Co1 model. -/
def icosianProjectiveToCo1 : IcosianProjectiveModel →* LeechCentralQuotient :=
  QuotientGroup.map _ _ icosianHermitianToCo0 (le_of_eq icosianCentralSigns_eq_comap)

theorem icosianProjectiveToCo1_injective : Function.Injective icosianProjectiveToCo1 := by
  apply (MonoidHom.ker_eq_bot_iff icosianProjectiveToCo1).mp
  rw [icosianProjectiveToCo1,QuotientGroup.ker_map,← icosianCentralSigns_eq_comap]
  exact QuotientGroup.map_mk'_self _

theorem icosianProjectiveToCo1_mk (g : icosianHermitianGroup) :
    icosianProjectiveToCo1 (icosianProjectiveProjection g)=
      leechCentralProjection (icosianHermitianToCo0 g) := rfl

end Atlas.Conway
