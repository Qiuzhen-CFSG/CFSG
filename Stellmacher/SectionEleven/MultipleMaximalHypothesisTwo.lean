module

public import Stellmacher.SectionFiveToSeven.Result5_1
public import Stellmacher.SectionEleven.MultipleMaximalSetup
public import Stellmacher.SectionEleven.SylowTerminalContext

/-!
# The Sylow pair under the global local hypotheses

The first reduction of Section Eleven combines (5.1) with the existence of
distinct maximal two-locals over the fixed Sylow subgroup. The common subgroup
is the entire Sylow subgroup. The global local hypothesis supplies the
Baumann-local condition directly, without an odd-core quotient or a Baumann
stability assertion. The resulting graph is on the actual generated join.

Source: `refs/latex/stellmacher-n-group.tex`, Section Eleven, first paragraphs.
-/

namespace Stellmacher.SectionEleven

open SectionsFiveToSeven

universe u

public theorem multiple_maximal_hypothesisTwo
    {H : Type u} [Group H] [Finite H]
    (S0 : Sylow 2 H) (h : HypothesisOne H S0)
    (hLocal : ∀ U : Subgroup H, IsTwoLocal U →
      Group.IsSolvable U ∧ IsCharacteristicTwoType U)
    (hmax : ∃ M1 M2 : Subgroup H, M1 ≠ M2 ∧ IsMaximalTwoLocal M1 ∧
      IsMaximalTwoLocal M2 ∧ (S0 : Subgroup H) ≤ M1 ∧ (S0 : Subgroup H) ≤ M2) :
    ∃ P1 P2 : Subgroup H, HypothesisTwo H S0 (S0 : Subgroup H) P1 P2 := by
  obtain ⟨M1, M2, hne, hM1, hM2, hS1, hS2⟩ := hmax
  obtain ⟨S, P1, P2, hfive⟩ := lemma_five_one S0 h
  have hS := fiveOne_sylow_eq_of_multiple_maximal hfive hne ⟨hM1, hS1⟩ ⟨hM2, hS2⟩
  subst S
  exact ⟨P1, P2, h, hfive, fun U hU _ => hLocal U hU⟩

public theorem multiple_maximal_terminal_context
    {H : Type u} [Group H] [Finite H]
    (S0 : Sylow 2 H) (h : HypothesisOne H S0)
    (hLocal : ∀ U : Subgroup H, IsTwoLocal U →
      Group.IsSolvable U ∧ IsCharacteristicTwoType U)
    (hmax : ∃ M1 M2 : Subgroup H, M1 ≠ M2 ∧ IsMaximalTwoLocal M1 ∧
      IsMaximalTwoLocal M2 ∧ (S0 : Subgroup H) ≤ M1 ∧ (S0 : Subgroup H) ≤ M2) :
    ∃ P1 P2 : Subgroup H, Nonempty (SylowTerminalContext H S0 P1 P2) := by
  obtain ⟨P1, P2, hyp⟩ := multiple_maximal_hypothesisTwo S0 h hLocal hmax
  exact ⟨P1, P2, sylow_terminal_context hyp⟩

end Stellmacher.SectionEleven
