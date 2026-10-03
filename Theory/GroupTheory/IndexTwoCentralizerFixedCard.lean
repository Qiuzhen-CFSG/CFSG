module

public import Theory.GroupAction.IndexTwoFixedCard
public import Theory.GroupAction.SubgroupConjugation

/-!
# Centralizer counts for an index-two action

An elementary binary subgroup normalized by S and centralized by an
index-two subgroup of S has order at most the square of its centralizer
of S. This transports the involution fixed-point count to actual ambient
subgroups, as used in Parrott (1972), p.676.
-/

namespace Subgroup

/-- Ambient-subgroup form of the index-two fixed-point bound. -/
public theorem card_le_centralizer_card_sq_of_relIndex_two
    {G : Type*} [Group G] [Finite G]
    (A B S : Subgroup G) [IsElementaryAbelian 2 A]
    (hSA : S ≤ normalizer (A : Set G))
    (hAB : A ≤ centralizer (B : Set G)) (hindex : B.relIndex S = 2) :
    Nat.card A ≤ Nat.card ((centralizer (S : Set G)).subgroupOf A) ^ 2 := by
  let : MulDistribMulAction S A := conjMulDistribMulActionOfLeNormalizer S A hSA
  have hfix : ∀ n ∈ B.subgroupOf S, ∀ a : A, n • a = a := by
    intro n hn a
    apply Subtype.ext
    change (n : G) * (a : G) * (n : G)⁻¹ = (a : G)
    exact mul_inv_eq_iff_eq_mul.mpr (hAB a.property n hn)
  have hfixed : FixedPoints.subgroup S A = (centralizer (S : Set G)).subgroupOf A := by
    ext a
    constructor
    · intro ha s hs
      have hh := congrArg A.subtype (ha ⟨s, hs⟩)
      exact mul_inv_eq_iff_eq_mul.mp hh
    · intro ha s
      apply Subtype.ext
      change (s : G) * (a : G) * (s : G)⁻¹ = (a : G)
      exact mul_inv_eq_iff_eq_mul.mpr (ha s s.property)
  have hh := card_le_fixed_card_sq_of_index_two_kernel (B.subgroupOf S) hindex hfix
  rwa [hfixed] at hh

end Subgroup
