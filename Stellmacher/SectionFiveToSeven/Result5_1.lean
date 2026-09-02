module

public import Stellmacher.SectionFiveToSeven.Defs

open scoped Pointwise

namespace Stellmacher.SectionsFiveToSeven

universe u

/-- **Stellmacher (5.1).**  Under Hypothesis 1, the triple `(S,P₁,P₂)` and
one of the alternatives (a), (b), or (c₁)--(c₃) exist exactly as in the
paper. -/
public theorem lemma_five_one
    {H : Type u} [Group H] [Finite H]
    (S0 : Sylow 2 H) (h : HypothesisOne H S0) :
    ∃ (S P1 P2 : Subgroup H), FiveOneConditions H S0 S P1 P2 := by
  sorry

end Stellmacher.SectionsFiveToSeven
