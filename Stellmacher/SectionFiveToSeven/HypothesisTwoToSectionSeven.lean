module

public import Stellmacher.SectionFiveToSeven.Result5_3

/-!
# Passing from Hypothesis 2 to the Section 7 assumptions

This module packages the source transition from Hypothesis 2 to the standing
`SectionSevenHypotheses` used by the coset-graph arguments. Stellmacher (5.3)
supplies solvability and characteristic 2 type for the two amalgam members.
The remaining fields are the nontriviality and membership data already in
Hypothesis 2, the ambient 2-core conclusion from Hypothesis 1, and the explicit
generation hypothesis required by the current same-ambient Section 7
interface.

Source: `refs/latex/stellmacher-n-group.tex`, Hypothesis 2, (5.3), and the
standing assumptions at the start of Section 7.
-/

universe u

namespace Stellmacher.SectionsFiveToSeven.HypothesisTwo

/-- Hypothesis 2 supplies the Section 7 standing assumptions once the two
amalgam members are known to generate the ambient group. -/
public theorem sectionSevenHypotheses
    {H : Type u} [Group H] [Finite H]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    (h : HypothesisTwo H S0 S P1 P2)
    (hgenerated : P1 ⊔ P2 = ⊤) :
    SectionSevenHypotheses H S P1 P2 := by
  obtain ⟨hP1solvable, hP1char, hP2solvable, hP2char⟩ :=
    lemma_five_three S0 S P1 P2 h
  exact
    { S_nontrivial := h.fiveOne.S_nontrivial
      P1_mem := h.fiveOne.P1_mem
      P2_mem := h.fiveOne.P2_mem
      generated := hgenerated
      P1_solvable := hP1solvable
      P2_solvable := hP2solvable
      P1_characteristicTwo := hP1char
      P2_characteristicTwo := hP2char
      twoCore_eq_bot := h.hyp1.twoCore_eq_bot }

end Stellmacher.SectionsFiveToSeven.HypothesisTwo
