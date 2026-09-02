module

public import Stellmacher.SectionsOneToFourDefs

namespace Stellmacher.SectionFour

universe u

public structure LemmaFourOneConclusion
    {G : Type u} [Group G] [Finite G] (S : Sylow 2 G) : Prop where
  part_a :
    SectionThree.LSet (⊤ : Subgroup G) (S : Subgroup G) ≠ ∅ ∧
      SectionThree.PSet (⊤ : Subgroup G) (S : Subgroup G) ≠ ∅
  part_b : twoCoreAmbient (mSubgroup S) ≠ ⊥
  part_c : Subgroup.normalizer (S : Set G) ≤ mSubgroup S

/-! **Stellmacher (4.1).** -/
public theorem lemma_four_one
    {G : Type u} [Group G] [Finite G]
    (S : Sylow 2 G) (h : Hypotheses G S) :
    LemmaFourOneConclusion S := by
  sorry

end Stellmacher.SectionFour
