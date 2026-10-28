module

public import Theory.GroupTheory.Recognition.ReeTwo.CentricNormalizerReduction
public import Theory.GroupTheory.CentricRadicalCharacterFusion

/-!
# Ree two character fusion from an explicit candidate classification

Fix an actual involution centralizer isomorphism and either alternative binary
character. Suppose every centric intrinsic radical candidate is the Sylow
subgroup, the first parabolic core, or has characteristic restricted kernel.
Then invariance under the normalizer of the first parabolic core implies
invariance under all ambient conjugacy between Sylow elements, and hence under
every centric extremal normalizer.

The three classification branches use, respectively, the specified centralizer
action, the exceptional normalizer hypothesis, and characteristic-kernel
invariance. The intrinsic radical character fusion theorem assembles these
local checks. The classification and the choice of character remain explicit
inputs; neither ambient fusion nor candidate enumeration is assumed implicitly.

Source: van Beek (2024), Proposition 3.1, p. 10, for the local Ree two analysis;
the Alperin reduction refining Huppert X.4.7 is formalized in
`Theory.GroupTheory.CentricRadicalCharacterFusion`.
-/

namespace ReeTwo

section

variable {G : Type*} [Group G] [Finite G]
  (S : Sylow 2 G) (z : G) (hz : orderOf z = 2)
  (hcentral : (S : Subgroup G) ≤ Subgroup.centralizer {z})
  (ec : Subgroup.centralizer {z} ≃* Centralizer)
  (χ : SylowModel →* FiveFour.Cyclic 2)
  (hχ : χ = SylowModel.coreCharacter ∨ χ = SylowModel.mixedCharacter)

local notation "e" => sylowEquivOfCentralizer S z hcentral ec

include hz hχ

/-- With the intrinsic candidate classification supplied explicitly, the
exceptional normalizer is the only remaining check for ambient character fusion. -/
public theorem alternativeCharacter_eq_of_isConj_of_candidate_classification
    (hclass : ∀ (U : Subgroup G) (hUS : U ≤ (S : Subgroup G)),
      (S : Subgroup G) ⊓ Subgroup.centralizer (U : Set G) ≤ U →
      (((S : Subgroup G).subgroupOf (Subgroup.normalizer (U : Set G))).map
        U.normalizerMonoidHom ⊓ pCore 2 (MulAut U)) ≤
          (MulAut.conj : U →* MulAut U).range →
      U = (S : Subgroup G) ∨ U = firstParabolicCoreIn S e ∨
        ((χ.comp (e).toMonoidHom).comp (Subgroup.inclusion hUS)).ker.Characteristic)
    (hexceptional : NormalizerRespects S e χ (firstParabolicCoreIn S e))
    {x y : S} (hxy : IsConj (x : G) (y : G)) : χ (e x) = χ (e y) := by
  apply S.intrinsic_radical_character_fusion (χ.comp (e).toMonoidHom) ?_ hxy
  intro U hUS _ hcent hrad
  rcases hclass U hUS hcent hrad with rfl | rfl | hker
  · have hnormalizer := alternativeCharacters_respect_sylow_normalizer S z hz hcentral ec
    rcases hχ with rfl | rfl
    · exact hnormalizer.1
    · exact hnormalizer.2
  · exact hexceptional
  · exact normalizerRespects_of_characteristic_ker S e χ U hUS hker

/-- The same explicit classification and exceptional normalizer check imply
the centric extremal normalizer condition used by the common-character argument. -/
public theorem alternativeCharacter_centricNormalizerInvariant_of_candidate_classification
    (hclass : ∀ (U : Subgroup G) (hUS : U ≤ (S : Subgroup G)),
      (S : Subgroup G) ⊓ Subgroup.centralizer (U : Set G) ≤ U →
      (((S : Subgroup G).subgroupOf (Subgroup.normalizer (U : Set G))).map
        U.normalizerMonoidHom ⊓ pCore 2 (MulAut U)) ≤
          (MulAut.conj : U →* MulAut U).range →
      U = (S : Subgroup G) ∨ U = firstParabolicCoreIn S e ∨
        ((χ.comp (e).toMonoidHom).comp (Subgroup.inclusion hUS)).ker.Characteristic)
    (hexceptional : NormalizerRespects S e χ (firstParabolicCoreIn S e)) :
    CentricNormalizerInvariant S e χ := by
  intro _ _ _ _ g _ x y _ hxy
  apply alternativeCharacter_eq_of_isConj_of_candidate_classification
    S z hz hcentral ec χ hχ hclass hexceptional
  exact isConj_iff.mpr ⟨g⁻¹, by simpa only [inv_inv] using hxy⟩

end

end ReeTwo
