module

public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.PreciseMultiplierInputs.Reduction
public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.FittingReduction.Source
public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.ComponentDescent
public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.ExceptionalExtension

/-!
# The complete adequate B.5 induction with precise multiplier inputs

A.3.6 and the three-free perfect kernels of the actual binary derived G₂
group suffice for the high-rank argument. The genuine B.5.8 fitting theorem
and component descent then construct the original exceptional configuration
and its strictly smaller centralizer action. Strong induction discharges
every recursive-classification premise; the existing exceptional extension
endgame supplies every clause of the full adequate alternative.

All other universal earlier-source inputs are retained unchanged: B.5.1,
B.5.2, A.2.1, preparation B.5.5, B.1.9, A.1.31(1), and B.4.8(2–4).
The A.3.6 and binary-G₂ kernel producers are qt-a03-sqtk-structure and
qt-i01-a2-unitary-covers. The original full multiplier-table route remains
available. The full KnownSimple instantiation and discharge of these source
premises stay with qt-b05-general-classification.

Source: Aschbacher–Smith, A.3.6, pp.43–45, and B.5.3, B.5.6–12,
pp.104–110. The adopted outer alternative is the unchanged OuterSixThreeShape;
no additional fixed-space splitting is asserted.
-/

public section

open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
namespace CFSG.Quasithin.ChapterB.SourceInduction.PreciseMultiplierInputs
open HighThreeRank HighThreeRank.CoverCentralizer
open HighThreeRank.CoverCentralizer.SourceConstruction
open HighThreeRank.ModuleCalculation.NaturalReduction.ModelComparison
open ComponentReduction
universe u v

variable {G : Type u} [Group G] [Finite G] {K : GroupClass.{u}}
  {V : Type v} [AddCommGroup V] [Module (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V)

/-- B.5.8 centralization, the original component descent and strict smaller
classification construct every field of the exceptional configuration. -/
theorem exceptional_configuration
    (h1 : ProjectiveLine.QuasisimpleClassificationInput.{u,v} K)
    (h52 : CoverInput K)
    (hA : SemisimpleInput K)
    (h5 : PreliminaryActions.Preparation.ComponentInput.{u,v} K)
    (h36 : Chapter1.Section02.A36Input K)
    (hg : ThreeFreePerfectKernels.{u} (commutator (Atlas.G2.Model (ZMod 2))))
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
  have h3 : ∀ L, IsComponent G L → primeRank 3 L = 1 := fun L hL =>
    component_rank_eq_one ρ h1 h52 h5 hA h36 hg hyp hnot hL
  rcases subsingleton_or_nontrivial G with ht | hn
  · exact (hnot (Or.inl ht)).elim
  · let := hn
    obtain ⟨c⟩ := conclusion_of_source ρ h5 h1 h48two hA hyp
      (minimalBestOffender_centralizes_fitting_of_source ρ h19 h131 h48three hyp ih hnot) h3
    obtain ⟨hc, hlt, hh⟩ := c.nontrivial_descent ρ h5 h1 hyp (h3 _ c.isComponent) hnot
    let := hc
    have ha := (ih _ hlt _ _ hh).of_nontrivial _
    have hr : primeRank 3 c.component = 1 := h3 _ c.isComponent
    exact ⟨c, hr, hc, hlt, hh, ha, c.exceptional ρ h48three h131 h5 h1 hyp hr hnot ih⟩

variable (h1 : ProjectiveLine.QuasisimpleClassificationInput.{u,v} K)
    (h52 : CoverInput K)
    (hA : SemisimpleInput K)
    (h5 : PreliminaryActions.Preparation.ComponentInput.{u,v} K)
    (h36 : Chapter1.Section02.A36Input K)
    (hg : ThreeFreePerfectKernels.{u} (commutator (Atlas.G2.Model (ZMod 2))))
    (h48two : PreliminaryActions.ThreeCovers.CentralExtension.EarlierB48Two.{u,v})
    (h19 : FittingReduction.EarlierB19.{u,v})
    (h131 : FactorExtraction.EarlierA131One.{u})
    (h48three : FactorExtraction.EarlierB48Three.{u,v})
    (h48four : ExceptionalExtension.Nonsplit.EarlierB48Four.{u,v})

include h1 h52 hA h5 h36 hg h48two h19 h131 h48three h48four

/-- The full universal adequate B.5 classifier. Strong induction discharges
every recursive-classification premise, using the original action and the
strictly smaller actual centralizer supplied by component descent. -/
theorem adequateClassification_of_source : AdequateClassificationInput.{u,v} K := by
  suffices hall : ∀ n : ℕ, ∀ (D : Type u) [Group D] [Finite D], Nat.card D = n →
      ∀ (W : Type v) [AddCommGroup W] [Module (ZMod 2) W]
        (σ : Representation (ZMod 2) D W), FFHypothesis K σ → AdequateAlternative σ by
    intro D _ _ W _ _ σ hyp
    exact hall (Nat.card D) D rfl W σ hyp
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro D _ _ hcard W _ _ σ hyp
    by_cases ht : Subsingleton D
    · exact Or.inl ht
    have hsmall : SmallerClassification.{u,v} K (Nat.card D) := by
      intro E _ _ hlt X _ _ τ hh
      exact ih (Nat.card E) (hcard ▸ hlt) E rfl X τ hh
    by_contra hnot
    obtain ⟨c, hr, hn, _, _, _, he⟩ := exceptional_configuration σ
      h1 h52 hA h5 h36 hg h48two h19 h131 h48three hyp hnot hsmall
    let : Nontrivial (centralizer (c.first : Set D)) := hn
    obtain ⟨f⟩ := c.factor_module_second σ h48three h131 h5 h1 hyp hr hnot hsmall
    exact hnot (ExceptionalExtension.adequate_of_exceptional hyp h48three h48four c he f)

/-- Apply the complete sufficient-source induction to the original faithful
binary representation. The full KnownSimple instantiation remains with the
source assembly owner; no smaller catalogue is substituted for K. -/
theorem FFHypothesis.adequate_of_source (hyp : FFHypothesis K ρ) :
    AdequateAlternative ρ :=
  adequateClassification_of_source h1 h52 hA h5 h36 hg h48two h19 h131 h48three h48four
    G V ρ hyp

end CFSG.Quasithin.ChapterB.SourceInduction.PreciseMultiplierInputs
