module
public import CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.NonblockSourceContradictionOfMSData
public import CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.SourceSelectionOrdinaryComplete

/-!
# Original MS alternatives in the rank-one uniqueness assembly

Apply the action-only nonblock contradiction to the actual source configuration.
The original full SL₃ quotient, its nonbinary field and the whole-core
MSModuleAlternatives at an actual Sylow remain explicit. No secondary component,
strict core enlargement, quotient sieve, graph actor or representation model is
an additional premise. The completed source selection and ordinary/block
exclusions then give uniqueness over the same original L.

The full-quotient selection in original 4.3.8 remains with
qt-d-1222-rankone-uniqueness-nonblock; the genuine nonbinary C.1.34 alternatives
remain with qt-c134-nonbinary-linear-three-source. This specialized input is
only required for the original constrained nonblock configurations. It does not
assume or instantiate the refuted universal EarlierMSClassifications interface.
Consequently this conditional assembly does not assert unconditional 4.3.2.

Source: Aschbacher–Smith, original 4.3.2–16, pp.613–619; C.1.34, pp.136–137.
-/

@[expose] public section
open Subgroup Theory.GroupTheory ClassicalGroup
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness
open Chapter12.Section02
open Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- The remaining original input: a full nonbinary SL₃ quotient together with
the genuine whole-core alternatives at an actual Sylow of K O₂(I). The field,
marking, radical and Sylow in the alternatives are the same as in the source.
This is an earlier-source premise, not an asserted classification theorem. -/
def Nonblock.OriginalMSAlternatives (c : SourceConfiguration T L) : Prop :=
  ∃ F : ChapterB.QuasisimpleSource.BinaryField, 1 < F.degree ∧
    ∃ e : (Nonblock.K c ⧸ pCore 2 (Nonblock.K c)) ≃* SL(3,F.Carrier),
    ∃ P : Subgroup G, Chapter1.IsSylowIn 2 P (Nonblock.K c ⊔ c.I.pCoreIn 2) ∧
      MSModuleAlternatives (Nonblock.K c) (c.I.pCoreIn 2) P F.degree F.Carrier e

/-- Discharge the actual nonblock callback using only its original MS input.
All secondary-action and terminal contradiction premises are constructed. -/
theorem Nonblock.false_of_originalMSAlternatives
    (D : ChosenModule T L V) (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    {c : SourceConfiguration T L}
    (hf : generalizedFitting c.K = pCore 2 c.K) (hb : ¬ ChapterC.IsBlock c.K)
    (hms : Nonblock.OriginalMSAlternatives c) : False := by
  obtain ⟨F,hn,e,P,hP,hm⟩ := hms
  exact Nonblock.false_of_source_action_of_alternatives D h hf hb F.degree hn F rfl e P hP hm

/-- Uniqueness over the original L from genuine original MS alternatives.
Source selection and the ordinary/block exclusions are already proved. -/
theorem uniqueness_of_originalMSAlternatives
    (D : ChosenModule T L V) (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1 < n) (hpsl : IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    (hms : ∀ c : SourceConfiguration T L,
      generalizedFitting c.K = pCore 2 c.K → ¬ ChapterC.IsBlock c.K →
        Nonblock.OriginalMSAlternatives c) :
    ∀ X : Subgroup G, IsMaximalTwoLocal X → L ≤ X → X = normalizer (L : Set G) :=
  uniqueness_of_nonblock_exclusion D h hmany hn hpsl
    (fun c hf hb => Nonblock.false_of_originalMSAlternatives D h hf hb (hms c hf hb))

end CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness
