module

public import Stellmacher.SectionThree.LemmaThreeOne

open scoped BigOperators Pointwise

namespace Stellmacher.SectionThree

universe u

/-! **Stellmacher (3.2).** -/
public theorem lemma_three_two
    {G : Type u} [Group G] [Finite G]
    (S : Subgroup G) (h : Hypotheses G S)
    (L : Subgroup G) (hL : L ∈ LSet (⊤ : Subgroup G) S) :
    twoPrimeResidualAmbient L =
      ⨆ P : {P : Subgroup G // P ∈ PSet L S}, (P : Subgroup G) := by
  sorry

end Stellmacher.SectionThree
