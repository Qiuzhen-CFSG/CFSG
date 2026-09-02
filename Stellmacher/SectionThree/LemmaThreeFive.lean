module

public import Stellmacher.SectionThree.LemmaThreeFour

namespace Stellmacher.SectionThree

universe u

/-! **Stellmacher (3.5).**  `N` is kept in the ambient group, with its
relative normality in `P` made explicit. -/
public theorem lemma_three_five
    {G : Type u} [Group G] [Finite G]
    (S : Subgroup G) (h : Hypotheses G S)
    (P : Subgroup G) (hP : P ∈ PSet (⊤ : Subgroup G) S)
    (N : Subgroup G)
    (hN : N ≤ P ∧ N ≤ twoCoreAmbient P ∧ (N.subgroupOf P).Normal)
    (hsolv : Group.IsSolvable P)
    (hcentral : ⁅N, twoCoreAmbient P ⊓ twoResidualAmbient P⁆ = ⊥) :
    ⁅(Subgroup.center S).map S.subtype, twoResidualAmbient P⁆ ≠ ⊥ ∨
      ⁅N, twoResidualAmbient P⁆ = ⊥ := by
  sorry

end Stellmacher.SectionThree
