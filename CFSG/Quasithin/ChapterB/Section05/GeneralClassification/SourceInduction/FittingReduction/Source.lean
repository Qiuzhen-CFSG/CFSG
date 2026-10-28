module

public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.FittingReduction.FactorSelection
public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.FittingReduction.Assembly
public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.FactorExtraction
public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.CounterexampleReduction

/-!
# The B.5.8 source reduction and its component-recursion application

A minimal best offender that moves the Fitting subgroup selects the actual
S3 factor of B.1.9. Restricting the given SQTK cover bounds the complementary
three-rank, and induction applies only at that factor's strictly smaller order.
The proved factor extraction supplies every module alternative, including the
four-dimensional indecomposable quotient, contradicting the counterexample.

The final application supplies this centralization to the component recursion
and constructs the exceptional configuration remaining after B.5.12. All
classification parameters are genuine universal earlier-source implications;
no selected factor, rank bound or extraction assertion remains an input.

Source: Aschbacher--Smith, combined manuscript of 1 March 2004, B.5.8 and
B.5.11--12, printed pp.106 and 109. The final induction owner discharges the
smaller-order hypothesis and the earlier-source owners supply their implications.
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

/-- B.5.8, with the actual selected factor, cover-rank bound and rank-one
module extraction supplied by their proved source reductions. -/
theorem minimalBestOffender_centralizes_fitting_of_source
    (h19 : FittingReduction.EarlierB19.{u,v})
    (h131 : FactorExtraction.EarlierA131One.{u})
    (h48 : FactorExtraction.EarlierB48Three.{u,v})
    (hyp : FFHypothesis K ρ) (ih : SmallerClassification.{u,v} K (Nat.card G))
    (hnot : ¬ AdequateAlternative ρ)
    (A : Subgroup G) (hA : IsMinimalBestOffender ρ A) :
    A ≤ centralizer (fittingSubgroup G : Set G) := by
  by_contra hn
  obtain ⟨c⟩ := FittingReduction.FFHypothesis.fitting_configuration hyp h19 hA hn
  obtain ⟨cover⟩ := hyp.quotient
  have hr : primeRank 3 c.second ≤ 1 :=
    FactorExtraction.second_primeRank_le_one_of_symmetricThree h131 cover c.product
      c.firstEquiv.symm.toMonoidHom c.firstEquiv.symm.injective
  exact hnot (c.adequate hyp ih (FactorExtraction.rankOneModuleExtraction h48) hr)

/-- Actual B.5.9--12 application: source inputs and the strict smaller-order
induction construct the exceptional first-factor configuration. -/
theorem exceptional_configuration_of_source_counterexample
    (h1 : ProjectiveLine.QuasisimpleClassificationInput.{u,v} K)
    (h52 : CoverInput K) (h55 : ComponentsInput.{u,v} K)
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
  obtain ⟨c, hn, hlt, hh, hc⟩ := component_recursion_of_not_adequate ρ
    h1 h52 h55 hA hI h5 h48two hyp hnot
    (minimalBestOffender_centralizes_fitting_of_source ρ h19 h131 h48three hyp ih hnot) ih
  have hr : primeRank 3 c.component = 1 :=
    HighThreeRank.component_rank_eq_one_of_not_adequate ρ h1 h52 h55 hA hI hyp hnot
      c.isComponent
  exact ⟨c, hr, hn, hlt, hh, hc,
    c.exceptional ρ h48three h131 h5 h1 hyp hr hnot ih⟩

end CFSG.Quasithin.ChapterB.SourceInduction
