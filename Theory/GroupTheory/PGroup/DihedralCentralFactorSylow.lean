module

public import Theory.GroupTheory.PGroup.DihedralCentralFactor
public import Theory.GroupTheory.PGroup.RankTwoFour
public import Theory.GroupTheory.InvolutionTransfer
public import Theory.GroupTheory.PGroup.DihedralCyclicCentralFactorSylow
public import Theory.GroupTheory.PGroup.DihedralQuaternionCentralFactorSylow

/-!
# Excluding proper dihedral central factors in simple groups

For a Sylow two-subgroup of elementary rank at most two, a proper dihedral
central factor leaves either a cyclic center of order greater than two or
a generalized quaternion centralizer. In a finite simple ambient group,
the dihedral embedding rules out a normal subgroup of index two, so every
involution has an ambient conjugate in every index-two Sylow subgroup.

The centralizer is cyclic or generalized quaternion. The cyclic branch is
excluded by transfer and the quaternion branch by weak closure and Z-star.
Combining these ambient exclusions proves that the dihedral factor is the
whole Sylow subgroup. Both the Sylow rank bound and its ambient version are
provided below.

Source: MacWilliams's theorem as cited in Janko–Thompson, Math. Z. 113 (1970),
1.2, printed pp.385–386, reference [12] on p.397.
-/

namespace Sylow

open Subgroup

/-- The ambient rank bound gives the two precise proper-centralizer alternatives. -/
public theorem proper_dihedral_factor_centralizer_cases
    {G : Type*} [Group G] [Finite G]
    (S : Sylow 2 G)
    (hrank : ∀ A : Subgroup G, IsElementaryAbelian 2 A → Nat.card A < 8)
    (D : Subgroup S) (e : D ≃* DihedralGroup 4)
    (hgen : D ⊔ centralizer (D : Set S) = ⊤) (hproper : D ≠ ⊤) :
    (IsCyclic (centralizer (D : Set S)) ∧
      centralizer (D : Set S) = center S ∧ 2 < Nat.card (center S)) ∨
      ∃ n : ℕ, 3 ≤ n ∧
        Nonempty (centralizer (D : Set S) ≃* QuaternionGroup (2 ^ (n - 2))) :=
  Subgroup.proper_dihedral_factor_centralizer_cases S.isPGroup'
    (elementary_card_lt_eight_of_subgroup hrank (S : Subgroup G)) D e hgen hproper

/-- A dihedral subgroup in a simple group's Sylow rules out normal index two. -/
public theorem no_normal_index_two_of_dihedral_subgroup
    {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]
    (S : Sylow 2 G) (D : Subgroup S) (e : D ≃* DihedralGroup 4) :
    ∀ N : Subgroup G, N.Normal → N.index ≠ 2 := by
  have hD : Nat.card D = 8 := by
    rw [Nat.card_congr e.toEquiv, DihedralGroup.nat_card]
  have hlarge : 8 ≤ Nat.card G := by
    exact hD ▸ (D.card_le_card_group.trans (S : Subgroup G).card_le_card_group)
  intro N hN hi
  rcases hN.eq_bot_or_eq_top with hb | ht
  · have hc : Nat.card G = 2 := by simpa only [hb, index_bot] using hi
    omega
  · simp only [ht, index_top] at hi
    omega

/-- The involution-transfer consequence available before the remaining fusion analysis. -/
public theorem exists_isConj_mem_of_index_two_of_dihedral_subgroup
    {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]
    (S : Sylow 2 G) (D : Subgroup S) (e : D ≃* DihedralGroup 4)
    (U : Subgroup S) (hU : U.index = 2) (t : S) (ht : orderOf t = 2) :
    ∃ u : S, IsConj (t : G) (u : G) ∧ u ∈ U :=
  S.exists_isConj_mem_of_index_two
    (S.no_normal_index_two_of_dihedral_subgroup D e) U hU t ht

/-- Under the rank bound on the Sylow subgroup, a normal dihedral central
factor in a finite simple group is the whole Sylow subgroup. -/
public theorem dihedral_central_factor_eq_top_of_sylow_rank
    {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]
    (S : Sylow 2 G)
    (hrank : ∀ A : Subgroup S, IsElementaryAbelian 2 A → Nat.card A < 8)
    (D : Subgroup S) [D.Normal] (he : Nonempty (D ≃* DihedralGroup 4))
    (hgen : D ⊔ centralizer (D : Set S) = ⊤) : D = ⊤ := by
  obtain ⟨e⟩ := he
  rcases centralizer_cyclic_or_quaternion_of_dihedral S.isPGroup' hrank D e with
    hcyclic | ⟨n, hn, hf⟩
  · let := hcyclic
    exact S.dihedral_factor_eq_top_of_cyclic_centralizer hrank D e hgen
  · exact (S.dihedral_quaternion_central_factor_false hrank D e hgen n hn hf).elim

/-- Under the ambient elementary rank bound, a normal dihedral central factor
in a finite simple group's Sylow two-subgroup is the whole Sylow subgroup. -/
public theorem dihedral_central_factor_eq_top
    {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]
    (S : Sylow 2 G)
    (hrank : ∀ A : Subgroup G, IsElementaryAbelian 2 A → Nat.card A < 8)
    (D : Subgroup S) [D.Normal] (he : Nonempty (D ≃* DihedralGroup 4))
    (hgen : D ⊔ centralizer (D : Set S) = ⊤) : D = ⊤ :=
  S.dihedral_central_factor_eq_top_of_sylow_rank
    (elementary_card_lt_eight_of_subgroup hrank (S : Subgroup G)) D he hgen

end Sylow
