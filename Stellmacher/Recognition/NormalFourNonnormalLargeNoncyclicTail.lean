module

public import Stellmacher.Recognition.NormalFourNonnormalCoreSetup
public import Stellmacher.Recognition.NormalFourNonnormalLargeTailStructure
public import Stellmacher.Recognition.NormalFourNonnormalLargeTailWeakClosure
public import Stellmacher.Recognition.SimpleInvolutionFusion
public import Theory.GroupTheory.PGroup.NormalFourInvolutionFusion
public import Theory.GroupTheory.PGroup.ExtraspecialCentralProduct

/-!
# Exclusion of large noncyclic Hall tails

In the actual odd-core quotient, the core preimage contains the unique
normal four. Each central Sylow involution has a distinct ambient conjugate
in that four: otherwise commuting square roots extend weak closure to the
whole Sylow subgroup, contradicting Z-star. For a noncyclic Hall tail of
order at least sixteen, the structural index theorem and the power-subgroup
fusion calculation exclude such fusion inside the four. This contradiction
proves the strict tail bound. The index bound is derived from the action on
the core, rather than assumed.

This is an alternative endpoint to the elementary centralizer of order eight
in Janko–Thompson, Math. Z. 113 (1970), §4, Case 1, pp.392–393. It uses the
stronger elementary-rank bound and the intrinsic unique-normal-four square-root
theorem, without the subsequent transfer argument or any core-order bound.
Source: `refs/original/n-group-global/odd-core-rank-two-source/normal-four-case-split.md`.
-/

open Subgroup

namespace Stellmacher.Recognition

/-- The unique normal four contains a
distinct ambient conjugate of each central Sylow involution. -/
public theorem exists_distinct_isConj_in_unique_normal_four
    {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]
    (hns : ¬ Group.IsSolvable G)
    (hrank : ∀ U : Subgroup G, IsElementaryAbelian 2 U → Nat.card U < 8)
    (S : Sylow 2 G) (E : Subgroup S) [E.Normal] [IsElementaryAbelian 2 E]
    (hE : Nat.card E = 4)
    (hunique : ∀ F : Subgroup S, F.Normal → IsElementaryAbelian 2 F →
      Nat.card F = 4 → F = E)
    (z : S) (hzC : z ∈ center S) (hz : orderOf z = 2) :
    ∃ t : S, t ∈ E ∧ t ≠ z ∧ IsConj (z : G) (t : G) := by
  classical
  by_contra hnone
  have hweak (t : S) (htH : t ∈ E) (ht : IsConj (z : G) (t : G)) : t = z := by
    by_contra hne
    exact hnone ⟨t, htH, hne, ht⟩
  obtain ⟨t, hne, ht⟩ := exists_distinct_isConj_in_sylow hns S z hz
  exact hne (S.eq_of_isConj_of_weakly_closed_in_unique_normal_four_of_sylow_rank
    (elementary_card_lt_eight_of_subgroup hrank (S : Subgroup G)) E hE hunique
    z hzC hz hweak t ht)

namespace NormalFourCentralOmegaTwo

/-- The central involution has a distinct ambient conjugate inside the actual
core preimage, without any index assumption. -/
public theorem omegaCorePreimage_exists_distinct_isConj
    {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]
    (hns : ¬ Group.IsSolvable G) (hN : IsNTwoGroup G)
    (hrank : ∀ U : Subgroup G, IsElementaryAbelian 2 U → Nat.card U < 8)
    (S : Sylow 2 G) (hZ : Nat.card (omega₁ (center S) (p := 2)) = 2)
    (E : Subgroup S) [E.Normal] [IsElementaryAbelian 2 E] (hE : Nat.card E = 4)
    (hunique : ∀ F : Subgroup S, F.Normal → IsElementaryAbelian 2 F →
      Nat.card F = 4 → F = E) :
    ∃ z t : S, z ∈ center S ∧ orderOf z = 2 ∧ t ∈ omegaCorePreimage S ∧
      t ≠ z ∧ IsConj (z : G) (t : G) := by
  obtain ⟨w, hw⟩ := exists_prime_orderOf_dvd_card'
    (G := omega₁ (center S) (p := 2)) 2 (by rw [hZ])
  let z : S := (w : center S)
  have hz : orderOf z = 2 := (orderOf_coe (w : center S)).trans
    ((orderOf_coe w).trans hw)
  have hzC : z ∈ center S := (w : center S).property
  obtain ⟨t, htH, hne, hconj⟩ := exists_distinct_isConj_in_unique_normal_four
    hns hrank S E hE hunique z hzC hz
  exact ⟨z, t, hzC, hz, four_le_omegaCorePreimage hN hrank S hZ E hE htH, hne, hconj⟩

set_option linter.unusedVariables false in
/-- A large noncyclic Hall tail would both force and exclude fusion of the
central involution into a distinct element of the unique normal four.
The full width-one interface is retained for the noncyclic-tail assembly. -/
public theorem omegaQuotient_noncyclicHallTail_card_lt_sixteen
    {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]
    (hns : ¬ Group.IsSolvable G) (hN : IsNTwoGroup G)
    (hrank : ∀ U : Subgroup G, IsElementaryAbelian 2 U → Nat.card U < 8)
    (S : Sylow 2 G) (hnonab : ¬ IsMulCommutative S)
    (hZ : Nat.card (omega₁ (center S) (p := 2)) = 2)
    (E : Subgroup S) [E.Normal] [IsElementaryAbelian 2 E] (hE : Nat.card E = 4)
    (hunique : ∀ F : Subgroup S, F.Normal → IsElementaryAbelian 2 F →
      Nat.card F = 4 → F = E)
    (hnormal : ¬ (fourImage S E).Normal)
    (hwidth : ∀ A D : Subgroup (pCore 2 (OmegaQuotient S)),
      A.Normal → D.Normal → IsExtraspecial 2 A → IsBinaryHallFactor D →
      D ≤ centralizer (A : Set (pCore 2 (OmegaQuotient S))) → A ⊔ D = ⊤ →
      Nat.card A ≠ 32)
    (A D : Subgroup (pCore 2 (OmegaQuotient S))) [A.Normal] [D.Normal]
    [IsExtraspecial 2 A] (hA : Nat.card A = 8)
    (hD : IsBinaryHallFactor D) (hn : ¬ IsCyclic D)
    (hc : D ≤ centralizer (A : Set (pCore 2 (OmegaQuotient S))))
    (hg : A ⊔ D = ⊤) : Nat.card D < 16 := by
  by_contra hsmall
  have hlarge : 16 ≤ Nat.card D := Nat.le_of_not_gt hsmall
  have hi := omegaCorePreimage_index_le_two_of_large_noncyclic_tail
    hN hrank S hZ E hunique hnormal A D hA hD hn hc hg hlarge
  obtain ⟨w, hw⟩ := exists_prime_orderOf_dvd_card'
    (G := omega₁ (center S) (p := 2)) 2 (by rw [hZ])
  let z : S := (w : center S)
  have hz : orderOf z = 2 := (orderOf_coe (w : center S)).trans
    ((orderOf_coe w).trans hw)
  have hzC : z ∈ center S := (w : center S).property
  obtain ⟨t, htE, hne, hconj⟩ := exists_distinct_isConj_in_unique_normal_four
    hns hrank S E hE hunique z hzC hz
  exact hne (eq_of_isConj_in_four_of_large_noncyclic_tail
    hN hrank S hZ E hE hunique hnormal hi A D hD hn hc hg hlarge
    z t hzC hz htE hconj)

end NormalFourCentralOmegaTwo
end Stellmacher.Recognition
