module

public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleNaturalFixedQuotientQuinticOddPlacement
public import Theory.GroupTheory.CComponent.CoreCentralNormalizer

/-!
# The original Sylow normalizes the odd linear-two component

The original quintic residual lies in K and has nontrivial core-central
action. Any element of T moving K would place that residual in two distinct
component factors, making the action trivial. Thus this same T normalizes K.

Source: Aschbacher--Smith 6.1.4, printed p.666.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
attribute [local instance] Representation.SL2.BinarySmall.spaceBinaryModule
namespace CFSG.Quasithin.Chapter6.Source.RankOneRecognition
open RankOneGeneric
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L M V M₁ K : Subgroup G} {n : ℕ}

/-- The full original Sylow subgroup preserves the original outside
component after the odd linear-two placement. -/
theorem original_hermitian_odd_linear_component_normalized_by_sylow
    (h : Hypothesis611 KnownSimple.IsKnownSimple T L M V n)
    (hout : Chapter3.HasMaximalOutside T M)
    (hm : IsConjugationModel L (reducedSubgroup (L ⊔ (T : Subgroup G)))
      (Representation.SL2.BinarySmall.hermitian 2))
    (hM₁ : IsMaximalTwoLocal M₁) (hCM₁ : omegaCentralizer T ≤ M₁)
    (hK : K ∈ Chapter1.cComponentsIn M₁) (hnot : ¬ K ≤ M)
    (hq : IsQuasisimple (K ⧸ pCore 2 K))
    (p d : ℕ) (hp : p.Prime) (ho : Odd p) (hd : d = 1 ∨ d = 2)
    (hc : ClassicalGroup.IsPSL (coreCentralQuotient K) 2 (p^d)) :
    (T : Subgroup G) ≤ normalizer (K : Set G) := by
  let := hq
  have hXK := original_hermitian_quintic_le_odd_linear_component
    h hout hm hM₁ hCM₁ hK hnot hq p d hp ho hd hc
  have hfive := original_hermitian_quintic_odd_linear_image_card
    h hout hm hM₁ hCM₁ hK hnot hq p d hp ho hd hc
  have hne : coreCentralActorImage K (quinticResidual T L) ≠ ⊥ := by
    intro he
    rw [he,card_bot] at hfive
    omega
  exact (le_inf (sylow_le_omegaCentralizer.trans hCM₁)
    (sylow_normalizes_quinticResidual (h.rankOneInput hout).sylow_normalizes)).trans
      (normalizer_inf_le_of_coreCentral_image_ne_bot M₁ K (quinticResidual T L)
        hK.1 hK.2 hXK hne)

end CFSG.Quasithin.Chapter6.Source.RankOneRecognition
