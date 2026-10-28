module

public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleNaturalFixedQuotientQuinticEffectiveFactor
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanGlobalPrimeJankoFourLocal

/-!
# Excluding the original Janko four carrier

The original effective factor theorem supplies the literal normal simple
carrier, a faithful order-five actor, the actual effective Sylow, and their
permuting product of order dividing `2^a * 5`. The native J₄ Sylow-overgroup
calculation excludes five in every full-Sylow subgroup with this order bound.
No maximal-cover premise or arbitrary Sylow replacement is used.

Source: Aschbacher--Smith 6.1.4 and A.3.15, printed pp.665 and 50--51;
GLS3 Table 5.3i.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
attribute [local instance] Representation.SL2.BinarySmall.spaceBinaryModule
namespace CFSG.Quasithin.Chapter6.Source.RankOneRecognition
open RankOneGeneric
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L M V M₁ K : Subgroup G} {n : ℕ}

/-- The original outside component's central carrier cannot be J₄. -/
theorem original_hermitian_component_not_jankoFour
    (h : Hypothesis611 KnownSimple.IsKnownSimple T L M V n)
    (hout : Chapter3.HasMaximalOutside T M)
    (hm : IsConjugationModel L (reducedSubgroup (L ⊔ (T : Subgroup G)))
      (Representation.SL2.BinarySmall.hermitian 2))
    (hM₁ : IsMaximalTwoLocal M₁) (hCM₁ : omegaCentralizer T ≤ M₁)
    (hK : K ∈ Chapter1.cComponentsIn M₁) (hnot : ¬ K ≤ M)
    (hq : IsQuasisimple (K ⧸ pCore 2 K)) :
    ¬ Nonempty (coreCentralQuotient K ≃* Janko4.Model) := by
  rintro ⟨e⟩
  obtain ⟨E,S,a,hN,⟨eN⟩,hE,hcent,hcard⟩ :=
    original_hermitian_quintic_effective_factor h hout hm hM₁ hCM₁ hK hnot hq
  let := hN
  exact CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Prime.JankoFourActors.no_five_actor _ E S (eN.trans e) hE
    (by rw [hcent]; exact disjoint_bot_right) hcard

end CFSG.Quasithin.Chapter6.Source.RankOneRecognition
