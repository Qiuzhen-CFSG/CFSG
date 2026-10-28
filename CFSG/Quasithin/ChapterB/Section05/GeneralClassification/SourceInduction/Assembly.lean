module

public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.FittingReduction.PreparationInput
public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.ExceptionalExtension

/-!
# The complete conditional adequate B.5.6 induction

Strong induction on the order of the actual finite actor binds
`SmallerClassification`. The trivial actor is included explicitly. For a
counterexample, the proved B.5.8--12 reductions construct the exceptional
first factor and the strictly smaller centralizer acting on its literal fixed
space. The proved rank-one extraction supplies the second factor module, and
the complete exceptional endgame contradicts the counterexample. Both the
Fitting reduction and component recursion can use classification only after
proving a strict decrease of group order.

`adequateClassification_of_source` proves the existing universal adequate
classifier. Its two action-level applications retain every source module
clause, with exactly `OuterSixThreeShape` in the adopted outer branch. The
original whole-space outer splitting and its obstruction remain separate.

Only genuine universal earlier-source implications remain as parameters:
* full corrected B.5.1 (`qt-b05-quasisimple`);
* full B.5.2 and the single preparation B.5.5 input
  (`qt-b05-quotient-components`);
* A.2.1 (`qt-a-02`) and the complete I.1.3 multiplier table
  (`qt-i-01`, including `qt-i01-lie-a2`);
* B.1.9 (`qt-b01-fitting-structure`) and A.1.31(1)
  (`qt-a-01-section-rank`);
* B.4.8(2--4) (`qt-b-04-natural-extensions`).
The B.4.8(3) parameter also supplies the definitionally identical exceptional
extension input. No second B.5.5 presentation, selected factor, complementary
rank, extraction, cohomology, splitting, or recursive-classification premise
remains. Instantiating these earlier inputs for the full known-simple class
belongs to `qt-b05-general-classification`.

Source: Aschbacher--Smith, combined manuscript of 1 March 2004,
B.5.3 and B.5.6--12, printed pp.104--110.
-/

public section

open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
namespace CFSG.Quasithin.ChapterB.SourceInduction
open HighThreeRank.CoverCentralizer.SourceConstruction
open HighThreeRank.ModuleCalculation.NaturalReduction.ModelComparison.BinaryG2Exclusion
open ComponentReduction
universe u v

variable {K : GroupClass.{u}}
    (h1 : ProjectiveLine.QuasisimpleClassificationInput.{u,v} K)
    (h52 : CoverInput K)
    (hA : SemisimpleInput K) (hI : EarlierMultiplierInput K)
    (h5 : PreliminaryActions.Preparation.ComponentInput.{u,v} K)
    (h48two : PreliminaryActions.ThreeCovers.CentralExtension.EarlierB48Two.{u,v})
    (h19 : FittingReduction.EarlierB19.{u,v})
    (h131 : FactorExtraction.EarlierA131One.{u})
    (h48three : FactorExtraction.EarlierB48Three.{u,v})
    (h48four : ExceptionalExtension.Nonsplit.EarlierB48Four.{u,v})

include h1 h52 hA hI h5 h48two h19 h131 h48three h48four

/-- The universal adequate B.5.6 implication from the genuine earlier-source
inputs. Strong induction discharges every smaller-classification premise. -/
theorem adequateClassification_of_source : AdequateClassificationInput.{u,v} K := by
  suffices hall : ∀ n : ℕ, ∀ (G : Type u) [Group G] [Finite G], Nat.card G = n →
      ∀ (V : Type v) [AddCommGroup V] [Module (ZMod 2) V]
        (ρ : Representation (ZMod 2) G V), FFHypothesis K ρ → AdequateAlternative ρ by
    intro G _ _ V _ _ ρ hyp
    exact hall (Nat.card G) G rfl V ρ hyp
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro G _ _ hcard V _ _ ρ hyp
    by_cases ht : Subsingleton G
    · exact Or.inl ht
    have hsmall : SmallerClassification.{u,v} K (Nat.card G) := by
      intro E _ _ hlt X _ _ σ hh
      exact ih (Nat.card E) (hcard ▸ hlt) E rfl X σ hh
    by_contra hnot
    obtain ⟨c, hr, hn, _, _, _, he⟩ := exceptional_configuration_of_preparation ρ
      h1 h52 hA hI h5 h48two h19 h131 h48three hyp hnot hsmall
    let : Nontrivial (centralizer (c.first : Set G)) := hn
    obtain ⟨f⟩ := c.factor_module_second ρ h48three h131 h5 h1 hyp hr hnot hsmall
    exact hnot (ExceptionalExtension.adequate_of_exceptional hyp h48three h48four c he f)

variable {G : Type u} [Group G] [Finite G]
    {V : Type v} [AddCommGroup V] [Module (ZMod 2) V]
    {ρ : Representation (ZMod 2) G V}

/-- Apply the assembled induction to the original faithful binary action and
its actual finite SQTK quotient presentation, including the trivial actor. -/
theorem FFHypothesis.adequate_of_source (hyp : FFHypothesis K ρ) :
    AdequateAlternative ρ :=
  adequateClassification_of_source h1 h52 hA hI h5 h48two h19 h131 h48three h48four
    G V ρ hyp

/-- For a nontrivial actor, the assembled source induction yields all five
nontrivial adequate alternatives with their original actions and subspaces. -/
theorem FFHypothesis.nontrivial_adequate_of_source [Nontrivial G]
    (hyp : FFHypothesis K ρ) : NontrivialAdequateAlternative ρ :=
  (hyp.adequate_of_source h1 h52 hA hI h5 h48two h19 h131 h48three h48four).of_nontrivial ρ

end CFSG.Quasithin.ChapterB.SourceInduction
