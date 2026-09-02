module

public import Stellmacher.SectionThree.LemmaThreeSeven

open scoped BigOperators Pointwise

namespace Stellmacher.SectionThree

universe u

public structure LemmaThreeEightConclusion
    {G : Type u} [Group G] [Finite G]
    (S P₁ P₂ H N Q H₀ H₁ : Subgroup G) : Prop where
  chain : Q ≤ N ∧ N ≤ H₀ ∧ H₀ ≤ H₁ ∧ H₁ ≤ H
  normal_series :
    (Q.subgroupOf N).Normal ∧ (N.subgroupOf H₀).Normal ∧
      (H₀.subgroupOf H₁).Normal ∧ (H₁.subgroupOf H).Normal
  part_a :
    Q = S ⊓ N ∧ (Q.subgroupOf H).Normal ∧
      ∀ K : Subgroup G, K ≤ S → K ≤ H → (K.subgroupOf H).Normal → K ≤ Q
  part_b :
    IsMinimalNormalOver N H H₀ ∧
      (twoResidualAmbient P₁ ≤ H₀ ∨ twoResidualAmbient P₂ ≤ H₀)
  part_c :
    H₁ = H₀ ∨
      (H₁ = H₀ ⊔ twoResidualAmbient P₁ ∧
        ¬ twoResidualAmbient P₁ ≤ H₀) ∨
      (H₁ = H₀ ⊔ twoResidualAmbient P₂ ∧
        ¬ twoResidualAmbient P₂ ≤ H₀)
  part_d : (H : Set G) = (S : Set G) * (H₁ : Set G)

/-! **Stellmacher (3.8).** -/
public theorem lemma_three_eight
    {G : Type u} [Group G] [Finite G]
    (S : Subgroup G) (h : Hypotheses G S)
    (P₁ P₂ H N : Subgroup G)
    (hP₁ : P₁ ∈ PSet (⊤ : Subgroup G) S)
    (hP₂ : P₂ ∈ PSet (⊤ : Subgroup G) S)
    (hH : H = P₁ ⊔ P₂)
    (hN : N ≤ H ∧ (N.subgroupOf H).Normal ∧
      ¬ twoResidualAmbient P₁ ≤ N ∧
      ¬ twoResidualAmbient P₂ ≤ N ∧
      ∀ N' : Subgroup G, N ≤ N' → N' ≤ H →
        (N'.subgroupOf H).Normal →
        (¬ twoResidualAmbient P₁ ≤ N' ∧
          ¬ twoResidualAmbient P₂ ≤ N') → N' = N)
    (hsolv₁ : Group.IsSolvable P₁)
    (hsolv₂ : Group.IsSolvable P₂) :
    ∃ Q H₀ H₁ : Subgroup G,
      LemmaThreeEightConclusion S P₁ P₂ H N Q H₀ H₁ := by
  sorry

end Stellmacher.SectionThree
