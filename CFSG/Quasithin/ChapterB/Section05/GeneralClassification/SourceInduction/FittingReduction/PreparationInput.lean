module

public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.FittingReduction.Source
public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.CounterexampleReduction.PreparationInput

/-!
# The exceptional source configuration from a single B.5.5 input

B.5.8 centralization and the single-input component recursion construct the
actual B.5.9--12 configuration. The high-rank and component reductions now share
the literal chief-section input, removing the need to prove a second equivalent
classifier presentation. Every genuine earlier-source premise and the strict
smaller-order induction remain explicit for their existing assembly owners.

Source: Aschbacher--Smith, combined 1 March 2004 manuscript, B.5.8--12,
printed pp.106--109.
-/

public section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
namespace CFSG.Quasithin.ChapterB.SourceInduction
open HighThreeRank.CoverCentralizer.SourceConstruction
open HighThreeRank.ModuleCalculation.NaturalReduction.ModelComparison.BinaryG2Exclusion
open ComponentReduction
universe u v
variable {G : Type u} [Group G] [Finite G]
  {V : Type v} [AddCommGroup V] [Module (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V) {K : GroupClass.{u}}

/-- Actual B.5.9--12 application: source inputs and the strict smaller-order
induction construct the exceptional first-factor configuration. -/
theorem exceptional_configuration_of_preparation
    (h1 : ProjectiveLine.QuasisimpleClassificationInput.{u,v} K)
    (h52 : CoverInput K)
    (hA : SemisimpleInput K) (hI : EarlierMultiplierInput K)
    (h5 : PreliminaryActions.Preparation.ComponentInput.{u,v} K)
    (h48two : PreliminaryActions.ThreeCovers.CentralExtension.EarlierB48Two.{u,v})
    (h19 : FittingReduction.EarlierB19.{u,v})
    (h131 : FactorExtraction.EarlierA131One.{u})
    (h48three : FactorExtraction.EarlierB48Three.{u,v})
    (hyp : FFHypothesis K ρ) (hnot : ¬ AdequateAlternative ρ)
    (ih : SmallerClassification.{u,v} K (Nat.card G)) :
    ∃ c : Conclusion ρ,
      primeRank 3 c.component = 1 ∧
      Nontrivial (centralizer (c.first : Set G)) ∧
      Nat.card (centralizer (c.first : Set G)) < Nat.card G ∧
      FFHypothesis K (c.productConfiguration.fixed.toRepresentation.comp
        (centralizer (c.first : Set G)).subtype) ∧
      NontrivialAdequateAlternative (c.productConfiguration.fixed.toRepresentation.comp
        (centralizer (c.first : Set G)).subtype) ∧
      IsExceptional ρ c.first c.sectionData.space := by
  obtain ⟨c, hn, hlt, hh, hc⟩ := component_recursion_of_preparation ρ
    h1 h52 hA hI h5 h48two hyp hnot
    (minimalBestOffender_centralizes_fitting_of_source ρ h19 h131 h48three hyp ih hnot) ih
  have hr : primeRank 3 c.component = 1 :=
    HighThreeRank.component_rank_eq_one_of_preparation ρ h1 h52 h5 hA hI hyp hnot
      c.isComponent
  exact ⟨c, hr, hn, hlt, hh, hc,
    c.exceptional ρ h48three h131 h5 h1 hyp hr hnot ih⟩

end CFSG.Quasithin.ChapterB.SourceInduction
