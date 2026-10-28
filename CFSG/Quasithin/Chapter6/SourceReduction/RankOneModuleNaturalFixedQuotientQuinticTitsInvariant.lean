module

public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleNaturalFixedQuotientQuinticTitsPlacement
public import Theory.GroupTheory.CComponent.CoreCentralNormalizer

/-!
# The original Sylow preserves its Tits component

The whole original quintic residual lies in K and has nontrivial image
on its central carrier. Component uniqueness therefore forces every
element of the original Sylow to preserve this same K. No component
orbit or Sylow subgroup is replaced.

Source: Aschbacher--Smith 6.1.4, printed p.666.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
attribute [local instance] Representation.SL2.BinarySmall.spaceBinaryModule
namespace CFSG.Quasithin.Chapter6.Source.RankOneRecognition
open RankOneGeneric Chapter1.Section02.LocalModels
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L M V M₁ K : Subgroup G} {n : ℕ}

/-- The original Sylow normalizes the original Tits component. -/
theorem original_hermitian_sylow_normalizes_tits_component
    (h : Hypothesis611 KnownSimple.IsKnownSimple T L M V n)
    (hout : Chapter3.HasMaximalOutside T M)
    (hm : IsConjugationModel L (reducedSubgroup (L ⊔ (T : Subgroup G)))
      (Representation.SL2.BinarySmall.hermitian 2))
    (hM₁ : IsMaximalTwoLocal M₁) (hCM₁ : omegaCentralizer T ≤ M₁)
    (hK : K ∈ Chapter1.cComponentsIn M₁) (hnot : ¬ K ≤ M)
    (hq : IsQuasisimple (K ⧸ pCore 2 K))
    (e : coreCentralQuotient K ≃* Tits.ParrottGroup) :
    (T : Subgroup G) ≤ normalizer (K : Set G) := by
  let X := quinticResidual T L
  have hXK := original_hermitian_quintic_le_tits_component
    h hout hm hM₁ hCM₁ hK hnot hq e
  obtain ⟨D,hD,_,hDX,_,_,_⟩ := original_hermitian_quintic_torus h hout hm
  have himage := original_hermitian_quintic_central_image_card
    h hout hm hM₁ hCM₁ hK hnot hq D hD hDX
  have hne : coreCentralActorImage K X ≠ ⊥ := by
    intro he
    have hle : coreCentralActorImage K D ≤ coreCentralActorImage K X :=
      map_mono (subgroupOf_mono (normalizer (K : Set G)) hDX)
    have hb : coreCentralActorImage K D = ⊥ := bot_unique (he ▸ hle)
    rw [hb,card_bot] at himage
    omega
  have hTM₁ : (T : Subgroup G) ≤ M₁ := sylow_le_omegaCentralizer.trans hCM₁
  have hTX : (T : Subgroup G) ≤ normalizer (X : Set G) :=
    sylow_normalizes_quinticResidual (h.rankOneInput hout).sylow_normalizes
  exact (le_inf hTM₁ hTX).trans
    (normalizer_inf_le_of_coreCentral_image_ne_bot M₁ K X hK.1 hK.2 hXK hne)

end CFSG.Quasithin.Chapter6.Source.RankOneRecognition
