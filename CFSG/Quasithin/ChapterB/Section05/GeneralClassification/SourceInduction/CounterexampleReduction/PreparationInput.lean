module

public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.HighThreeRank
public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.ComponentDescent

/-!
# Component recursion from one B.5.5 source input

The high-rank reduction uses the positive component rank and generalized-Fitting
identity supplied by the same chief-section input used in B.5.9--11. It therefore
constructs the actual strictly smaller complementary FF action without a second
encoding of the B.5.5 classifier. The original action, quotient and component
maps are unchanged. The smaller-order classification is applied only after
strict cardinal descent is proved.

Source: Aschbacher--Smith, combined 1 March 2004 manuscript, B.5.7--11,
printed pp.105--109. B.5.8 centralization and genuine earlier-source inputs
remain explicit here; the fitting-source consumer supplies centralization.
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
theorem component_descent_of_preparation
    (h1 : ProjectiveLine.QuasisimpleClassificationInput.{u,v} K)
    (h52 : CoverInput K)
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
    HighThreeRank.component_rank_eq_one_of_preparation ρ h1 h52 h5 hA hI hyp hnot hL
  rcases subsingleton_or_nontrivial G with ht | hn
  · exact (hnot (Or.inl ht)).elim
  · let := hn
    obtain ⟨c⟩ := conclusion_of_source ρ h5 h1 h48 hA hyp hfit h3
    exact ⟨c, c.nontrivial_descent ρ h5 h1 hyp (h3 _ c.isComponent) hnot⟩

/-- The recursive classification is invoked only after constructing all
hypotheses and strict cardinal descent for the actual centralizer factor. -/
theorem component_recursion_of_preparation
    (h1 : ProjectiveLine.QuasisimpleClassificationInput.{u,v} K)
    (h52 : CoverInput K)
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
    component_descent_of_preparation ρ h1 h52 hA hI h5 h48 hyp hnot hfit
  let := hn
  exact ⟨c, hn, hlt, hh, (ih _ hlt _ _ hh).of_nontrivial _⟩

end CFSG.Quasithin.ChapterB.SourceInduction
