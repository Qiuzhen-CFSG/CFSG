module

public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleNaturalFixedQuotientQuinticEffectiveFactor
public import Theory.Mathieu.M12.QuinticSylowActors

/-!
# Excluding the original Mathieu twelve carrier

The original faithful quintic actor permutes with the actual effective
Sylow subgroup. Their join has order a power of two times five. The native
M₁₂ Sylow overgroup calculation excludes this action on the literal inner
simple factor of the component's core-central quotient.

Source: Aschbacher--Smith 6.1.4 and A.3.15, printed pp.665 and 50--51.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
attribute [local instance] Representation.SL2.BinarySmall.spaceBinaryModule
namespace CFSG.Quasithin.Chapter6.Source.RankOneRecognition
open RankOneGeneric
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L M V M₁ K : Subgroup G} {n : ℕ}

/-- The original outside component's central carrier cannot be M₁₂. -/
theorem original_hermitian_component_not_mathieuTwelve
    (h : Hypothesis611 KnownSimple.IsKnownSimple T L M V n)
    (hout : Chapter3.HasMaximalOutside T M)
    (hm : IsConjugationModel L (reducedSubgroup (L ⊔ (T : Subgroup G)))
      (Representation.SL2.BinarySmall.hermitian 2))
    (hM₁ : IsMaximalTwoLocal M₁) (hCM₁ : omegaCentralizer T ≤ M₁)
    (hK : K ∈ Chapter1.cComponentsIn M₁) (hnot : ¬ K ≤ M)
    (hq : IsQuasisimple (K ⧸ pCore 2 K)) :
    ¬ Nonempty (coreCentralQuotient K ≃* Sporadic.Mathieu.M12) := by
  rintro ⟨e⟩
  obtain ⟨E,S,a,hN,⟨eN⟩,hE,hcent,hcard⟩ :=
    original_hermitian_quintic_effective_factor h hout hm hM₁ hCM₁ hK hnot hq
  let := hN
  exact Sporadic.Mathieu.M12QuinticSylowActors.no_five_actor _ E S
    ⟨eN.trans e⟩ hE (by rw [hcent]; exact disjoint_bot_right) hcard

end CFSG.Quasithin.Chapter6.Source.RankOneRecognition
