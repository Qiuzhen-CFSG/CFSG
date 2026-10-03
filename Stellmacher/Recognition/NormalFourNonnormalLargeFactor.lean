module

public import Stellmacher.Recognition.NormalFourNonnormalCoreSetup
public import Stellmacher.Recognition.NormalFourLargeCoreHigherIndex
public import Theory.GroupTheory.PGroup.RankTwoLargeExtraspecialFactor
public import Theory.GroupTheory.PGroup.DihedralQuaternionCentralFactorSylow
public import Stellmacher.Recognition.SimpleInvolutionFusion

/-!
# The large extraspecial factor in the actual odd-core quotient

An order-thirty-two extraspecial factor in the Hall decomposition is the
entire two-core, not merely a subgroup of bounded order. This follows by
absorbing its commuting supplement under the elementary rank bound. The
result is transported to the actual core preimage in the original Sylow.

The rank-two classification retains the quaternion-eight/dihedral-eight
central product, while excluding the plus model. Once the whole-core
reduction is established, the ambient exclusion applies: fusion forces
transitivity on the three involutions of the normal four's centralizer,
contradicting its order-sixteen subgroup with only two square values.
This finishes the exclusion without any further core-index hypothesis.

Source: Janko–Thompson, Math. Z. 113 (1970), §4, pp.389–392, and
`refs/original/n-group-global/odd-core-rank-two-source/normal-four-case-split.md`.
-/

namespace Stellmacher.Recognition.NormalFourCentralOmegaTwo

open Subgroup

variable {G : Type*} [Group G] [Finite G]

/-- An order-thirty-two extraspecial factor is the entire actual quotient
two-core. No additional assumptions on its commuting supplement are needed. -/
public theorem omegaQuotient_large_factor_eq_top
    (hrank : ∀ U : Subgroup G, IsElementaryAbelian 2 U → Nat.card U < 8)
    (S : Sylow 2 G) (A D : Subgroup (pCore 2 (OmegaQuotient S)))
    [IsExtraspecial 2 A] (hA : Nat.card A = 32)
    (hc : D ≤ centralizer (A : Set (pCore 2 (OmegaQuotient S))))
    (hgen : A ⊔ D = ⊤) : A = ⊤ := by
  apply eq_top_of_extraspecial_card_thirty_two_of_central_product pCore_isPGroup
    (elementary_card_lt_eight_of_subgroup ?_ (pCore 2 (OmegaQuotient S))) A D hA hc hgen
  intro U hU
  let : IsElementaryAbelian 2 U := hU
  exact omegaQuotient_rank hrank S U

/-- Absorption gives extraspecial structure and order thirty-two for the whole
core in the literal quotient by the odd core. -/
public theorem omegaQuotient_large_factor_core
    (hrank : ∀ U : Subgroup G, IsElementaryAbelian 2 U → Nat.card U < 8)
    (S : Sylow 2 G) (A D : Subgroup (pCore 2 (OmegaQuotient S)))
    [IsExtraspecial 2 A] (hA : Nat.card A = 32)
    (hc : D ≤ centralizer (A : Set (pCore 2 (OmegaQuotient S))))
    (hgen : A ⊔ D = ⊤) :
    IsExtraspecial 2 (pCore 2 (OmegaQuotient S)) ∧
      Nat.card (pCore 2 (OmegaQuotient S)) = 32 := by
  have htop := omegaQuotient_large_factor_eq_top hrank S A D hA hc hgen
  let e : A ≃* pCore 2 (OmegaQuotient S) :=
    (MulEquiv.subgroupCongr htop).trans Subgroup.topEquiv
  exact ⟨IsExtraspecial.of_mulEquiv e inferInstance, (Nat.card_congr e.toEquiv).symm.trans hA⟩

/-- The same large core is realized faithfully inside the original Sylow,
where ambient involution fusion must be analyzed. -/
public theorem omegaCorePreimage_large_factor
    (hrank : ∀ U : Subgroup G, IsElementaryAbelian 2 U → Nat.card U < 8)
    (S : Sylow 2 G) (A D : Subgroup (pCore 2 (OmegaQuotient S)))
    [IsExtraspecial 2 A] (hA : Nat.card A = 32)
    (hc : D ≤ centralizer (A : Set (pCore 2 (OmegaQuotient S))))
    (hgen : A ⊔ D = ⊤) :
    IsExtraspecial 2 (omegaCorePreimage S) ∧ Nat.card (omegaCorePreimage S) = 32 := by
  obtain ⟨he, hcard⟩ := omegaQuotient_large_factor_core hrank S A D hA hc hgen
  exact ⟨he.of_mulEquiv (omegaCorePreimageEquiv S).symm,
    (card_omegaCorePreimage S).trans hcard⟩

/-- The large extraspecial core cannot already be the Sylow subgroup: its
dihedral-quaternion structure would supply a weakly closed involution. -/
public theorem not_extraspecial_thirty_two_sylow [IsSimpleGroup G]
    (hns : ¬ Group.IsSolvable G)
    (hrank : ∀ U : Subgroup G, IsElementaryAbelian 2 U → Nat.card U < 8)
    (S : Sylow 2 G) [IsExtraspecial 2 S] (hS : Nat.card S = 32)
    (E : Subgroup S) [IsElementaryAbelian 2 E] (hE : Nat.card E = 4) : False := by
  have hr := elementary_card_lt_eight_of_subgroup hrank (S : Subgroup G)
  have hnot : ¬ E ≤ center S := by
    intro h
    have hh := card_le_of_le h
    rw [hE, IsExtraspecial.center_order_p 2 S] at hh
    omega
  obtain ⟨t, ht, htZ⟩ := SetLike.not_le_iff_exists.mp hnot
  obtain ⟨D, ⟨e⟩, hZD, hgen⟩ := IsExtraspecial.exists_dihedral_factor_of_noncentral_involution
    t (elemPow_eq_one_of_isElementaryAbelian t ht) htZ
  let C := centralizer (D : Set S)
  have hpow (c : C) : c ^ 4 = 1 := Subtype.ext (IsExtraspecial.pow_four_eq_one (c : S))
  rcases (S.isPGroup'.to_subgroup C).isCyclic_or_quaternion_two_of_no_elementary_four
      hpow (no_elementary_four_centralizer_of_dihedral hr D e) with hcyc | hquat
  · let : IsCyclic C := hcyc
    have hC : C = center S := centralizer_eq_center_of_dihedral_factor_of_isCyclic D hgen
    have htop : D = ⊤ := by
      apply top_unique
      rw [← hgen]
      exact sup_le le_rfl (by change C ≤ D; rw [hC]; exact hZD)
    have hh : Nat.card D = 8 := by rw [Nat.card_congr e.toEquiv, DihedralGroup.nat_card]
    rw [htop, Nat.card_congr Subgroup.topEquiv.toEquiv, hS] at hh
    omega
  · obtain ⟨f⟩ := hquat
    obtain ⟨z, hz, -, hclosed⟩ :=
      S.exists_weakly_closed_involution_of_dihedral_quaternion_factor D e hgen 2 (by decide) f
    obtain ⟨u, huz, hzu⟩ := exists_distinct_isConj_in_sylow hns S z hz
    exact huz (hclosed u hzu)

/-- In the large-factor case the actual core preimage is proper in the
original Sylow, before any analysis of the remaining relative indices. -/
public theorem omegaCorePreimage_large_factor_ne_top [IsSimpleGroup G]
    (hns : ¬ Group.IsSolvable G)
    (hrank : ∀ U : Subgroup G, IsElementaryAbelian 2 U → Nat.card U < 8)
    (S : Sylow 2 G) (E : Subgroup S) [IsElementaryAbelian 2 E] (hE : Nat.card E = 4)
    (A D : Subgroup (pCore 2 (OmegaQuotient S)))
    [IsExtraspecial 2 A] (hA : Nat.card A = 32)
    (hc : D ≤ centralizer (A : Set (pCore 2 (OmegaQuotient S))))
    (hgen : A ⊔ D = ⊤) : omegaCorePreimage S ≠ ⊤ := by
  intro htop
  obtain ⟨he, hcard⟩ := omegaCorePreimage_large_factor hrank S A D hA hc hgen
  let e : omegaCorePreimage S ≃* S := (MulEquiv.subgroupCongr htop).trans Subgroup.topEquiv
  let : IsExtraspecial 2 S := he.of_mulEquiv e
  exact not_extraspecial_thirty_two_sylow hns hrank S
    ((Nat.card_congr e.toEquiv).symm.trans hcard) E hE

/-- Only index two and index at least four remain for a large extraspecial
core in the original Sylow. -/
public theorem omegaCorePreimage_large_factor_index_cases [IsSimpleGroup G]
    (hns : ¬ Group.IsSolvable G)
    (hrank : ∀ U : Subgroup G, IsElementaryAbelian 2 U → Nat.card U < 8)
    (S : Sylow 2 G) (E : Subgroup S) [IsElementaryAbelian 2 E] (hE : Nat.card E = 4)
    (A D : Subgroup (pCore 2 (OmegaQuotient S)))
    [IsExtraspecial 2 A] (hA : Nat.card A = 32)
    (hc : D ≤ centralizer (A : Set (pCore 2 (OmegaQuotient S))))
    (hgen : A ⊔ D = ⊤) :
    (omegaCorePreimage S).index = 2 ∨ 4 ≤ (omegaCorePreimage S).index := by
  have hne := omegaCorePreimage_large_factor_ne_top hns hrank S E hE A D hA hc hgen
  obtain ⟨n, hn⟩ := S.isPGroup'.index (omegaCorePreimage S)
  have hn0 : n ≠ 0 := by
    intro h
    apply hne
    exact index_eq_one.mp (by simpa only [h, pow_zero] using hn)
  by_cases hn1 : n = 1
  · left
    simpa only [hn1, pow_one] using hn
  · right
    rw [hn]
    exact Nat.pow_le_pow_right (n := 2) (by decide) (show 2 ≤ n by omega)

/-- An extraspecial factor of order thirty-two in the actual quotient core
is impossible. First absorb its commuting supplement, then apply the ambient
exclusion to the whole core. -/
public theorem omegaQuotient_large_factor_false [IsSimpleGroup G]
    (hns : ¬ Group.IsSolvable G) (hN : IsNTwoGroup G)
    (hrank : ∀ U : Subgroup G, IsElementaryAbelian 2 U → Nat.card U < 8)
    (S : Sylow 2 G) (hZ : Nat.card (omega₁ (center S) (p := 2)) = 2)
    (E : Subgroup S) [E.Normal] [IsElementaryAbelian 2 E] (hE : Nat.card E = 4)
    (hunique : ∀ F : Subgroup S, F.Normal → IsElementaryAbelian 2 F →
      Nat.card F = 4 → F = E)
    (A D : Subgroup (pCore 2 (OmegaQuotient S)))
    [IsExtraspecial 2 A] (hA : Nat.card A = 32)
    (hc : D ≤ centralizer (A : Set (pCore 2 (OmegaQuotient S))))
    (hgen : A ⊔ D = ⊤) : False := by
  obtain ⟨he, hcard⟩ := omegaQuotient_large_factor_core hrank S A D hA hc hgen
  let : IsExtraspecial 2 (pCore 2 (OmegaQuotient S)) := he
  exact normal_four_large_core_false hns hN hrank S hZ E hE hunique hcard

/-- The large-extraspecial-factor exclusion with the full normal-four Hall
decomposition interface. The stronger theorem above does not require
normality or a binary Hall presentation of the commuting factors. -/
public theorem normal_four_large_factor_false [IsSimpleGroup G]
    (hns : ¬ Group.IsSolvable G) (hN : IsNTwoGroup G)
    (hrank : ∀ U : Subgroup G, IsElementaryAbelian 2 U → Nat.card U < 8)
    (S : Sylow 2 G) (_hnonab : ¬ IsMulCommutative S)
    (hZ : Nat.card (omega₁ (center S) (p := 2)) = 2)
    (E : Subgroup S) [E.Normal] [IsElementaryAbelian 2 E] (hE : Nat.card E = 4)
    (hunique : ∀ F : Subgroup S, F.Normal → IsElementaryAbelian 2 F →
      Nat.card F = 4 → F = E)
    (_hnormal : ¬ (fourImage S E).Normal)
    (A D : Subgroup (pCore 2 (OmegaQuotient S))) [A.Normal] [D.Normal]
    [IsExtraspecial 2 A] (hA : Nat.card A = 32) (_hD : IsBinaryHallFactor D)
    (hc : D ≤ centralizer (A : Set (pCore 2 (OmegaQuotient S))))
    (hgen : A ⊔ D = ⊤) : False := by
  exact omegaQuotient_large_factor_false hns hN hrank S hZ E hE hunique A D hA hc hgen

end Stellmacher.Recognition.NormalFourCentralOmegaTwo
