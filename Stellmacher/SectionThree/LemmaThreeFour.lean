module

public import Stellmacher.SectionThree.LemmaThreeThree

namespace Stellmacher.SectionThree

universe u

/-! **Stellmacher (3.4).** -/
public theorem lemma_three_four
    {G : Type u} [Group G] [Finite G]
    (S : Subgroup G) (h : Hypotheses G S)
    (P : Subgroup G) (hP : P ∈ PSet (⊤ : Subgroup G) S)
    (T : Subgroup G)
    (hT : T ≤ S ∧ (T.subgroupOf S).Normal)
    (hsolv : Group.IsSolvable P) :
    T ≤ twoCoreAmbient P ∨
      ⁅twoResidualAmbient P, T⁆ = twoResidualAmbient P := by
  sorry

end Stellmacher.SectionThree
