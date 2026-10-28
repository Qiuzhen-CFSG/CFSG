module

public import Stellmacher.SectionFiveToSeven.Defs

/-!
# Section 3 hypotheses supplied by Hypothesis 2

This module connects the standing assumptions of Stellmacher's Sections 5--7
to the minimal input used by the Section 3 results.  Hypothesis 1 supplies the
even order of the ambient group, while (5.1) supplies a nontrivial subgroup
`S`.  Since `P₁` belongs to `PFamily (⊤) S`, its defining Sylow witness
exhibits `S` as the ambient image of a Sylow 2-subgroup of `P₁`; mapping that
Sylow subgroup along the inclusion proves that `S` is a 2-group.

Thus the bridge preserves the exact subgroup `S` and uses no numbered result.
It supports later applications of the Section 3 lemmas under Hypothesis 2.

Source: Hypothesis 2 and the data supplied by Stellmacher (5.1) in
`refs/latex/stellmacher-n-group.tex`.
-/

namespace Stellmacher.SectionsFiveToSeven

universe u

namespace HypothesisTwo

/-- Hypothesis 2 supplies the even-order and nontrivial 2-subgroup assumptions
used throughout Section 3, for the same subgroup `S`. -/
public theorem sectionThreeHypotheses
    {H : Type u} [Group H] [Finite H]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    (h : HypothesisTwo H S0 S P1 P2) :
    SectionThree.Hypotheses H S := by
  refine
    { even_order := h.hyp1.even_order
      nontrivial_two_subgroup := ⟨h.fiveOne.S_nontrivial, ?_⟩ }
  obtain ⟨-, T, hT⟩ := h.fiveOne.P1_mem.1.2.1
  rw [← hT]
  exact T.isPGroup'.map P1.subtype

end HypothesisTwo

end Stellmacher.SectionsFiveToSeven
