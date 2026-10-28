module

public import Stellmacher.SectionEleven.TheoremOneSetup
public import Stellmacher.SectionFiveToSeven.Result5_1
public import Stellmacher.SectionEleven.MultipleMaximalSetup
public import Stellmacher.SectionEleven.SylowTerminalContext

/-!
# The actual terminal context under Theorem 1

The original Baumann-local assumption and two distinct maximal two-locals
containing the prescribed Sylow produce a native terminal context. The proved
setup gives Hypothesis 1, and (5.1) supplies its actual local pair. The two
maximal locals rule out (5.1)(c), so the pair's common subgroup is the entire
original Sylow. The source-correct Baumann definition then supplies exactly
Hypothesis 2's remaining local condition. The existing graph construction
forms the terminal context on the actual generated join of this pair.

This is the case-(i) reduction at the opening of Section 11 in
`refs/latex/stellmacher-n-group.tex`. No selected pair, ambient N2 hypothesis,
or classification result is an input.
-/

namespace Stellmacher.SectionEleven

open SectionsFiveToSeven

universe u

/-- The full original hypotheses of Theorem 1 provide an actual terminal graph
on a selected pair whose common Sylow is the prescribed Sylow subgroup. -/
public theorem theorem_one_terminal_context
    {H : Type u} [Group H] [Finite H]
    (S0 : Sylow 2 H)
    (hlocal : ∀ U : Subgroup H,
      IsTwoLocal U → baumannSubgroup S0 ≤ U →
      Group.IsSolvable U ∧ IsCharacteristicTwoType U)
    (hmax : ∃ M1 M2 : Subgroup H,
      M1 ≠ M2 ∧ IsMaximalTwoLocal M1 ∧ IsMaximalTwoLocal M2 ∧
      (S0 : Subgroup H) ≤ M1 ∧ (S0 : Subgroup H) ≤ M2) :
    ∃ P1 P2 : Subgroup H, Nonempty (SylowTerminalContext H S0 P1 P2) := by
  have hHyp := hypothesis_one_of_theorem_one_hypotheses S0 hlocal hmax
  obtain ⟨S, P1, P2, hFive⟩ := lemma_five_one S0 hHyp
  obtain ⟨M1, M2, hne, hM1, hM2, hS1, hS2⟩ := hmax
  have hS := fiveOne_sylow_eq_of_multiple_maximal hFive hne ⟨hM1, hS1⟩ ⟨hM2, hS2⟩
  subst S
  have hTwo : HypothesisTwo H S0 (S0 : Subgroup H) P1 P2 :=
    ⟨hHyp, hFive, fun U hU hB => hlocal U hU hB⟩
  exact ⟨P1, P2, sylow_terminal_context hTwo⟩

end Stellmacher.SectionEleven
