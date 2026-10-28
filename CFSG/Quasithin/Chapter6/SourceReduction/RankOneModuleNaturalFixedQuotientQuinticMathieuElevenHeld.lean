module

public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleNaturalFixedQuotientQuinticEffectiveFactor
public import Theory.Mathieu.M11.QuinticSylowActors
public import Theory.SpecificGroups.Held.QuinticSylowActors

/-!
# Excluding the original M₁₁ and Held central carriers

The literal effective factor and faithful original five-image meet the native
full-Sylow order obstructions. In M₁₁ an order-eighty overgroup would have a
characteristic central involution and lie in its order-forty-eight centralizer.
In Held the native three-free Sylow-overgroup theorem makes it a two-group.
Both contradictions concern the same original outside component.

Source: Aschbacher--Smith 6.1.4 and A.3.15, printed pp.665 and 50--51.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
attribute [local instance] Representation.SL2.BinarySmall.spaceBinaryModule
namespace CFSG.Quasithin.Chapter6.Source.RankOneRecognition
open RankOneGeneric
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L M V M₁ K : Subgroup G} {n : ℕ}

/-- The original outside component's central carrier cannot be M₁₁. -/
theorem original_hermitian_component_not_mathieuEleven
    (h : Hypothesis611 KnownSimple.IsKnownSimple T L M V n)
    (hout : Chapter3.HasMaximalOutside T M)
    (hm : IsConjugationModel L (reducedSubgroup (L ⊔ (T : Subgroup G)))
      (Representation.SL2.BinarySmall.hermitian 2))
    (hM₁ : IsMaximalTwoLocal M₁) (hCM₁ : omegaCentralizer T ≤ M₁)
    (hK : K ∈ Chapter1.cComponentsIn M₁) (hnot : ¬ K ≤ M)
    (hq : IsQuasisimple (K ⧸ pCore 2 K)) :
    ¬ Nonempty (coreCentralQuotient K ≃* Sporadic.Mathieu.M11) := by
  rintro ⟨e⟩
  obtain ⟨E,S,a,hN,⟨eN⟩,hE,hcent,hcard⟩ :=
    original_hermitian_quintic_effective_factor h hout hm hM₁ hCM₁ hK hnot hq
  let := hN
  exact Sporadic.Mathieu.M11QuinticSylowActors.no_five_actor _ E S
    ⟨eN.trans e⟩ hE (by rw [hcent]; exact disjoint_bot_right) hcard


/-- The original outside component's central carrier cannot be Held. -/
theorem original_hermitian_component_not_held
    (h : Hypothesis611 KnownSimple.IsKnownSimple T L M V n)
    (hout : Chapter3.HasMaximalOutside T M)
    (hm : IsConjugationModel L (reducedSubgroup (L ⊔ (T : Subgroup G)))
      (Representation.SL2.BinarySmall.hermitian 2))
    (hM₁ : IsMaximalTwoLocal M₁) (hCM₁ : omegaCentralizer T ≤ M₁)
    (hK : K ∈ Chapter1.cComponentsIn M₁) (hnot : ¬ K ≤ M)
    (hq : IsQuasisimple (K ⧸ pCore 2 K)) :
    ¬ Nonempty (coreCentralQuotient K ≃* Held.He) := by
  rintro ⟨e⟩
  obtain ⟨E,S,a,hN,⟨eN⟩,hE,hcent,hcard⟩ :=
    original_hermitian_quintic_effective_factor h hout hm hM₁ hCM₁ hK hnot hq
  let := hN
  exact Held.QuinticSylowActors.no_five_actor _ E S
    ⟨eN.trans e⟩ hE (by rw [hcent]; exact disjoint_bot_right) hcard

end CFSG.Quasithin.Chapter6.Source.RankOneRecognition
