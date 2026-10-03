module

public import Stellmacher.SectionsOneToFourDefs

/-!
# Conclusion package for Stellmacher (3.8)

This module records the normal series and its four asserted properties from
Stellmacher (3.8).  It is separated from the proof module so scratch proofs and
later consumers can use the stable statement without importing the theorem
under construction.

Source: `refs/latex/stellmacher-n-group.tex`, statement (3.8), journal p. 23.
-/

open scoped Pointwise

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

end Stellmacher.SectionThree
