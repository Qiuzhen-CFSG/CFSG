module

public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleNaturalFixedQuotientStationaryAssembly
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleNaturalFixedQuotientA5Stationary
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleNaturalFixedQuotientFourHyperplaneSource

/-!
# Reduction of the exact original natural quotient to the Hermitian degree-four case

The stationary degree-two deleted row is excluded on the original layer.
Every invariant natural seed fills that layer, giving the exact omega-span
quotient. The remaining whole Hermitian reduced module has weak-closure
rank greater than one; outside half-degree two its actual Thompson bound
would make that rank one. Thus the only remaining failure is the literal
whole R₂(LT) Hermitian module for SL₂(16).

The subsequent outside-component and quintic-fusion argument is not claimed.
Source: Aschbacher--Smith 6.1.4, printed pp.664--666.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher Representation
open scoped IsMulCommutative
attribute [local instance] SL2.BinarySmall.spaceBinaryModule
namespace CFSG.Quasithin.Chapter6.Source.Hypothesis611
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L M V : Subgroup G} {n : ℕ}

/-- From the original hypotheses, the sole remaining failure of the exact
natural omega quotient has degree four and a whole Hermitian R₂(LT) model. -/
theorem omega_natural_or_hermitian_four_enlargement
    (h : Hypothesis611 KnownSimple.IsKnownSimple T L M V n)
    (hout : Chapter3.HasMaximalOutside T M) :
    IsNaturalFixedQuotient L
      (conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) L) n ∨
    (n = 4 ∧ elementaryAbelianMaxJ (T : Subgroup G) ≤
      centralizer (reducedSubgroup (L ⊔ (T : Subgroup G)) : Set G) ∧
      IsConjugationModel L (reducedSubgroup (L ⊔ (T : Subgroup G)))
        (SL2.BinarySmall.hermitian 2)) := by
  by_cases hn : n = 2
  · let hR := h.reduced_enlargement
    by_cases hj : elementaryAbelianMaxJ (T : Subgroup G) ≤
        centralizer (reducedSubgroup (L ⊔ (T : Subgroup G)) : Set G)
    · have hm := RankOneRecognition.original_stationary_degree_two_natural
        hR hout (hj.trans (centralizer_le hR.layer_le_V)) hn
      exact Or.inl (h.omega_natural_fixed_quotient_of_stationary_natural_enlargement hout hj hm)
    · exact Or.inl (hR.omega_natural_fixed_quotient_of_thompson_moves hout hj)
  · rcases h.omega_natural_or_hermitian_enlargement_of_degree_ne_two hout hn with hm | hherm
    · exact Or.inl hm
    · obtain ⟨s,he,hs,hj,hm⟩ := hherm
      let : NeZero s := ⟨by omega⟩
      have hs2 : s = 2 := by
        by_contra hne
        have hr := RankOneRecognition.full_reduced_hermitian_one_lt_globalR h hout hm hs
        have hLayer := RankOneRecognition.full_reduced_hermitian_layer_eq h hm
        have hmLayer := hm
        rw [←hLayer] at hmLayer
        have hr1 := RankOneRecognition.original_hermitian_layer_globalR
          h.reduced_enlargement hout hmLayer hs hne
        rw [hLayer] at hr1
        rw [hr1] at hr
        exact (lt_irrefl 1 hr)
      subst s
      exact Or.inr ⟨he,hj,hm⟩

/-- Outside the genuine degree-four obstruction, the original omega-span
has the required natural fixed quotient with no model premise. -/
theorem omega_natural_fixed_quotient_of_degree_ne_four
    (h : Hypothesis611 KnownSimple.IsKnownSimple T L M V n)
    (hout : Chapter3.HasMaximalOutside T M) (hn : n ≠ 4) :
    IsNaturalFixedQuotient L
      (conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) L) n :=
  (h.omega_natural_or_hermitian_four_enlargement hout).resolve_right (fun hh => hn hh.1)

end CFSG.Quasithin.Chapter6.Source.Hypothesis611
