module

public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.HighThreeRank
public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.ComponentDescent

/-!
# The assembled component recursion after B.5.8

The high-three-rank proof discharges the rank-one condition on every component.
The component reduction then selects a genuine minimal offender and moved
component, proves all five B.5.9 alternatives, and constructs the exact B.5.10
product. The complementary factor is nontrivial and strictly smaller, and its
restricted action satisfies every B.5.3 hypothesis. Only then is the induction
hypothesis applied to that factor.

The missing B.5.8 conclusion that minimal offenders centralize F(G) is explicit;
it remains to be proved by the final source induction. No B.5.7 or B.5.9–11
reduction or current-order classifier is assumed. The smaller-order recursion
must be bound by the final strong induction on Nat.card G.

Earlier-source inventory: complete universal B.5.1, B.5.2, B.5.5 (in the two
existing faithful-chief-section encodings), A.2.1, I.1.3, and B.4.8(2).
Their respective producers are qt-b05-quasisimple, qt-b05-quotient-components,
qt-a-02, qt-i-01, and qt-b-04-natural-extensions / qt-b-04. The universal
inputs' final discharge remains with qt-b05-general-classification.

Source: Aschbacher–Smith, combined 1 March 2004 manuscript, B.5.7–11,
printed pp.105–109.
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

/-- A counterexample with B.5.8 established has the literal component
configuration and a nontrivial strictly smaller complementary FF action. -/
theorem component_descent_of_not_adequate
    (h1 : ProjectiveLine.QuasisimpleClassificationInput.{u,v} K)
    (h52 : CoverInput K) (h55 : ComponentsInput.{u,v} K)
    (hA : SemisimpleInput K) (hI : EarlierMultiplierInput K)
    (h5 : PreliminaryActions.Preparation.ComponentInput.{u,v} K)
    (h48 : PreliminaryActions.ThreeCovers.CentralExtension.EarlierB48Two.{u,v})
    (hyp : FFHypothesis K ρ) (hnot : ¬ AdequateAlternative ρ)
    (hfit : ∀ A, IsMinimalBestOffender ρ A →
      A ≤ centralizer (fittingSubgroup G : Set G)) :
    ∃ c : Conclusion ρ,
      Nontrivial (centralizer (c.first : Set G)) ∧
      Nat.card (centralizer (c.first : Set G)) < Nat.card G ∧
      FFHypothesis K (c.productConfiguration.fixed.toRepresentation.comp
        (centralizer (c.first : Set G)).subtype) := by
  have h3 : ∀ L, IsComponent G L → primeRank 3 L = 1 := fun L hL =>
    HighThreeRank.component_rank_eq_one_of_not_adequate ρ h1 h52 h55 hA hI hyp hnot hL
  rcases subsingleton_or_nontrivial G with ht | hn
  · exact (hnot (Or.inl ht)).elim
  · let := hn
    obtain ⟨c⟩ := conclusion_of_source ρ h5 h1 h48 hA hyp hfit h3
    exact ⟨c, c.nontrivial_descent ρ h5 h1 hyp (h3 _ c.isComponent) hnot⟩

/-- The recursive classification is invoked only after constructing all
hypotheses and strict cardinal descent for the actual centralizer factor. -/
theorem component_recursion_of_not_adequate
    (h1 : ProjectiveLine.QuasisimpleClassificationInput.{u,v} K)
    (h52 : CoverInput K) (h55 : ComponentsInput.{u,v} K)
    (hA : SemisimpleInput K) (hI : EarlierMultiplierInput K)
    (h5 : PreliminaryActions.Preparation.ComponentInput.{u,v} K)
    (h48 : PreliminaryActions.ThreeCovers.CentralExtension.EarlierB48Two.{u,v})
    (hyp : FFHypothesis K ρ) (hnot : ¬ AdequateAlternative ρ)
    (hfit : ∀ A, IsMinimalBestOffender ρ A →
      A ≤ centralizer (fittingSubgroup G : Set G))
    (ih : SmallerClassification.{u,v} K (Nat.card G)) :
    ∃ c : Conclusion ρ,
      Nontrivial (centralizer (c.first : Set G)) ∧
      Nat.card (centralizer (c.first : Set G)) < Nat.card G ∧
      FFHypothesis K (c.productConfiguration.fixed.toRepresentation.comp
        (centralizer (c.first : Set G)).subtype) ∧
      NontrivialAdequateAlternative (c.productConfiguration.fixed.toRepresentation.comp
        (centralizer (c.first : Set G)).subtype) := by
  obtain ⟨c, hn, hlt, hh⟩ :=
    component_descent_of_not_adequate ρ h1 h52 h55 hA hI h5 h48 hyp hnot hfit
  let := hn
  exact ⟨c, hn, hlt, hh, (ih _ hlt _ _ hh).of_nontrivial _⟩

end CFSG.Quasithin.ChapterB.SourceInduction
