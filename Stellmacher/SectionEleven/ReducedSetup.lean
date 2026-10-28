module

public import Stellmacher.SectionFiveToSeven.Defs
public import FeitThompson.BGsection6.Defs


/-!
# The reduced Section 11 setup

This module proves the first reduction in Section 11 of Stellmacher's paper.
For a group satisfying the displayed `(N₂)` local-solvability condition and
`O₂(H) = 1`, the absence of alternatives (d) and (e) in Theorem 2 supplies
Hypothesis 1 of Section 5.

The failure of alternative (e) makes the `2'`-core of every 2-local trivial,
and solvable centralizer control then makes every such subgroup characteristic
2. This stronger all-two-local conclusion supplies the Baumann-local field of
Hypothesis 2 for any actual (5.1) witness. Together with the direct
`O₂(H) = 1` assumption, it also supplies the fields of Hypothesis 1.
This is the reduction at
`refs/latex/stellmacher-n-group.tex`, lines 1964--1971, using Hypothesis 1 at
lines 1051--1060.
-/

namespace Stellmacher.SectionEleven

open Stellmacher.SectionsFiveToSeven

universe u

/-- Excluding alternative (e) controls every two-local, not only those over `S0`. -/
public theorem two_local_solvable_characteristicTwo_of_nTwo
    {H : Type u} [Group H] [Finite H]
    (hN2 : IsNTwoGroup H)
    (hNoOddCore : ¬ ∃ U : Subgroup H,
      IsTwoLocal U ∧ pPrimeCore 2 U ≠ ⊥)
    (U : Subgroup H) (hU : IsTwoLocal U) :
    Group.IsSolvable U ∧ IsCharacteristicTwoType U := by
  refine ⟨hN2 U hU, ?_⟩
  apply centralizer_pCore_le_pCore_of_pPrimeCore_eq_bot
  · exact hN2 U hU
  · by_contra hOddCore
    exact hNoOddCore ⟨U, hU, hOddCore⟩

/-- Under the reduced Theorem 2 hypotheses, Section 5's Hypothesis 1 holds. -/
public theorem hypothesis_one_of_nTwo
    {H : Type u} [Group H] [Finite H]
    (hN2 : IsNTwoGroup H)
    (hEven : Even (Nat.card H))
    (hTwoCore : pCore 2 H = ⊥)
    (S0 : Sylow 2 H)
    (hNoStronglyEmbedded : ¬ ∃ M : Subgroup H, IsStronglyEmbedded M)
    (hNoOddCore : ¬ ∃ U : Subgroup H,
      IsTwoLocal U ∧ pPrimeCore 2 U ≠ ⊥) :
    HypothesisOne H S0 where
  even_order := hEven
  local_solvable_characteristicTwo := by
    intro U hU _
    exact two_local_solvable_characteristicTwo_of_nTwo hN2 hNoOddCore U hU
  twoCore_eq_bot := hTwoCore
  no_strongly_embedded := hNoStronglyEmbedded

/-- An actual (5.1) witness satisfies Hypothesis 2 in the reduced N₂ setting. -/
public theorem hypothesis_two_of_nTwo_of_fiveOne
    {H : Type u} [Group H] [Finite H]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    (hN2 : IsNTwoGroup H)
    (hNoOddCore : ¬ ∃ U : Subgroup H,
      IsTwoLocal U ∧ pPrimeCore 2 U ≠ ⊥)
    (hHyp : HypothesisOne H S0)
    (hFive : FiveOneConditions H S0 S P1 P2) :
    HypothesisTwo H S0 S P1 P2 where
  hyp1 := hHyp
  fiveOne := hFive
  local_B := fun U hU _ =>
    two_local_solvable_characteristicTwo_of_nTwo hN2 hNoOddCore U hU

end Stellmacher.SectionEleven
