module

public import Stellmacher.SectionThree.LemmaThreeTwo

namespace Stellmacher.SectionThree

universe u

public structure LemmaThreeThreeConclusion
    {G : Type u} [Group G] [Finite G]
    (S P : Subgroup G) (P₀ B : Subgroup P) : Prop where
  part_a :
    ∃ p : ℕ, Nat.Prime p ∧ Odd p ∧
      IsPGroup p
        (twoResidualAmbient (⊤ : Subgroup (P ⧸ pCore 2 P)))
  part_b :
    IsIrreducibleSection (S.subgroupOf P) P₀ (twoResidualSubgroup P)
  part_c :
    P₀.map (QuotientGroup.mk' (pCore 2 P)) =
      frattiniAmbient
        (twoResidualAmbient (⊤ : Subgroup (P ⧸ pCore 2 P)))

/-! **Stellmacher (3.3).**  `B` is represented as a subgroup of the local
group `P`; the maximality and the definition of `P₀` are explicit. -/
public theorem lemma_three_three
    {G : Type u} [Group G] [Finite G]
    (S : Subgroup G) (h : Hypotheses G S)
    (P : Subgroup G) (hP : P ∈ PSet (⊤ : Subgroup G) S)
    (B P₀ : Subgroup P)
    (hB : IsCoatom B ∧ S.subgroupOf P ≤ B ∧
      ∀ B' : Subgroup P, IsCoatom B' → S.subgroupOf P ≤ B' → B' = B)
    (hP₀ : P₀ ≤ B ∧ P₀.Normal ∧
      ∀ N : Subgroup P, N.Normal → N ≤ B → N ≤ P₀)
    (hsolv : Group.IsSolvable P) :
    LemmaThreeThreeConclusion S P P₀ B := by
  sorry

end Stellmacher.SectionThree
