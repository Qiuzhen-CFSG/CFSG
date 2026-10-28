module

public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleNaturalFixedQuotientTitsCubicObstruction
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleNaturalFixedQuotientTitsCubicMovement
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleNaturalFixedQuotientQuinticLastModels
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleNaturalFixedQuotientQuinticJankoFour
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleNaturalFixedQuotientQuinticSelection
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleNaturalFixedQuotientDegreeFour

/-!
# The terminal contradiction for the original full Hermitian branch

The actual cubic torus moves the inner Sylow omega-center. In the Tits
case the same outside component centralizes that center, and the cubic
rank bound forces the torus to centralize it as well. This closes the
last component alternative. The original selection and the completed
component exclusions then rule out the whole Hermitian degree-four case.

Source: Aschbacher--Smith 6.1.4, printed pp.665--666, using A.3.18.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher Representation
attribute [local instance] SL2.BinarySmall.spaceBinaryModule
namespace CFSG.Quasithin.Chapter6.Source.RankOneRecognition
open RankOneGeneric
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L M V M₁ K : Subgroup G} {n : ℕ}

/-- The remaining Tits branch is contradictory on the original carrier. -/
theorem original_hermitian_tits_terminal_false
    (h : Hypothesis611 KnownSimple.IsKnownSimple T L M V n)
    (hout : Chapter3.HasMaximalOutside T M)
    (hm : IsConjugationModel L (reducedSubgroup (L ⊔ (T : Subgroup G)))
      (SL2.BinarySmall.hermitian 2))
    (hM₁ : IsMaximalTwoLocal M₁) (hCM₁ : omegaCentralizer T ≤ M₁)
    (hK : K ∈ Chapter1.cComponentsIn M₁) (hnot : ¬ K ≤ M)
    (hqK : IsQuasisimple (K ⧸ pCore 2 K))
    (e : coreCentralQuotient K ≃* Tits.ParrottGroup) : False := by
  obtain ⟨_,D,_,_,hDN,hres,hmove⟩ :=
    original_hermitian_inner_cubic_movement h hout hm
  exact hmove (original_hermitian_tits_inner_omega_cubic_residual_centralizes
    h hout hm hM₁ hCM₁ hK hnot hqK e D hDN hres)


/-- The original full reduced subgroup cannot be the Hermitian module at
half-degree two. All comparison subgroups are selected from the source. -/
theorem original_full_hermitian_two_excluded
    (h : Hypothesis611 KnownSimple.IsKnownSimple T L M V n)
    (hout : Chapter3.HasMaximalOutside T M) :
    ¬ IsConjugationModel L (reducedSubgroup (L ⊔ (T : Subgroup G)))
      (SL2.BinarySmall.hermitian 2) := by
  intro hm
  obtain ⟨M₁,K,_,hM₁,hCM₁,hK,hq,_,hnot,_⟩ :=
    original_hermitian_quintic_selection h hout hm
  rcases original_hermitian_component_jankoFour_or_tits
    h hout hm hM₁ hCM₁ hK hnot hq with hj | he
  · exact original_hermitian_component_not_jankoFour
      h hout hm hM₁ hCM₁ hK hnot hq hj
  · obtain ⟨e⟩ := he
    exact original_hermitian_tits_terminal_false h hout hm hM₁ hCM₁ hK hnot hq e

end CFSG.Quasithin.Chapter6.Source.RankOneRecognition

namespace CFSG.Quasithin.Chapter6.Source.Hypothesis611
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L M V : Subgroup G} {n : ℕ}

/-- Source 6.1.4 on the literal original omega-span, with the standing
outside-maximal witness retained and every module case discharged. -/
theorem omega_natural_fixed_quotient
    (h : Hypothesis611 KnownSimple.IsKnownSimple T L M V n)
    (hout : Chapter3.HasMaximalOutside T M) :
    IsNaturalFixedQuotient L
      (conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) L) n := by
  rcases h.omega_natural_or_hermitian_four_enlargement hout with hm | ⟨_,_,hm⟩
  · exact hm
  · exact (RankOneRecognition.original_full_hermitian_two_excluded h hout hm).elim

end CFSG.Quasithin.Chapter6.Source.Hypothesis611
