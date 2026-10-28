module

public import Stellmacher.Recognition.NormalFourLargeCoreActionSetup
public import Stellmacher.Recognition.NormalFourLargeCoreInvolutionFixed
public import Stellmacher.Recognition.SimpleInvolutionFusion
public import Theory.GroupTheory.InvolutionSquareSubgroupFusion
public import Theory.GroupTheory.PGroup.ExtraspecialIndexTwoFusion

/-!
# The index-two extraspecial fusion reduction

In the literal central-omega quotient, assume that the actual two-core is
extraspecial and has Sylow index two. Its central involution is central in the
original Sylow. Z-star gives a distinct ambient conjugate. Once fusion inside
the core is excluded, this conjugate lies outside the core; its centralizer is
then elementary. A core centralizer of order at least four contradicts the
ambient elementary rank bound.

Inside-core fusion exclusion is proved by transporting an involution
centralizer and comparing nontrivial squares in the two extraspecial copies.
The fixed-subgroup bound follows from displacement on the central quotient.
The final theorem discharges both inputs, without an outer-action hypothesis.
This is the index-two paragraph of Janko–Thompson, Math. Z. 113 (1970),
§4, printed p.389, stopping at the elementary eight. The subsequent S₅
outer-action calculation in the source belongs to index at least four.
-/

namespace Stellmacher.Recognition.NormalFourCentralOmegaTwo

open Subgroup

/-- Final index-two assembly with its two mathematical prerequisites exposed.
The core order is needed by the fixed-subgroup calculation, not this assembly. -/
public theorem large_core_index_two_false_of_inside_fusion_and_fixed_card
    {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]
    (hns : ¬ Group.IsSolvable G)
    (hrank : ∀ A : Subgroup G, IsElementaryAbelian 2 A → Nat.card A < 8)
    (S : Sylow 2 G) [IsExtraspecial 2 (pCore 2 (OmegaQuotient S))]
    (hindex : (pCore 2 (OmegaQuotient S)).relIndex (omegaQuotientSylow S) = 2)
    (hinside : ∀ z t : S, orderOf z = 2 → z ∈ center S → z ∈ omegaCorePreimage S →
      orderOf t = 2 → t ∈ omegaCorePreimage S → IsConj (z : G) (t : G) → t = z)
    (hfixed : ∀ t : S, orderOf t = 2 → t ∉ omegaCorePreimage S →
      4 ≤ Nat.card (omegaCorePreimage S ⊓ centralizer ({t} : Set S) : Subgroup S)) :
    False := by
  let H := omegaCorePreimage S
  let : IsExtraspecial 2 H :=
    IsExtraspecial.of_mulEquiv (omegaCorePreimageEquiv S).symm inferInstance
  let Z := (center H).map H.subtype
  let : Z.Normal := ConjAct.normal_of_characteristic_of_normal
  have hZcard : Nat.card Z = 2 :=
    (card_map_of_injective H.subtype_injective).trans (IsExtraspecial.center_order_p 2 H)
  have hZcentral := central_of_normal_card_two Z hZcard
  obtain ⟨w, hw⟩ := exists_prime_orderOf_dvd_card' (G := center H) 2
    (by rw [IsExtraspecial.center_order_p 2 H])
  let z : H := w
  have hz : orderOf z = 2 := (orderOf_coe w).trans hw
  have hzc : (z : S) ∈ center S := hZcentral (mem_map_of_mem H.subtype w.property)
  have hzS : orderOf (z : S) = 2 := (orderOf_coe z).trans hz
  obtain ⟨t, htz, hzt⟩ := exists_distinct_isConj_in_sylow hns S z hzS
  have ht : orderOf t = 2 := by
    obtain ⟨g, hg⟩ := isConj_iff.mp hzt
    rw [← orderOf_coe t, ← hg, ← MulAut.conj_apply]
    simpa using ((MulAut.conj g).orderOf_eq ((z : S) : G)).trans
      ((orderOf_coe (z : S)).trans hzS)
  have hout : t ∉ H := fun hin => htz (hinside z t hzS hzc z.property ht hin hzt)
  apply S.not_isConj_of_extraspecial_index_two_of_inside_fusion_of_fixed_card
    (elementary_card_lt_eight_of_subgroup hrank (S : Subgroup G)) H
    ((index_omegaCorePreimage S).trans hindex) z hz hzc ?_ t
    (by simpa only [ht] using pow_orderOf_eq_one t) hout (hfixed t ht hout) hzt
  intro u hu hzu
  have hu2 : orderOf u = 2 := by
    obtain ⟨g, hg⟩ := isConj_iff.mp hzu
    rw [← orderOf_coe u, ← hg, ← MulAut.conj_apply]
    simpa using ((MulAut.conj g).orderOf_eq ((z : S) : G)).trans
      ((orderOf_coe (z : S)).trans hzS)
  exact hinside z u hzS hzc z.property hu2 hu hzu

/-- The literal quotient two-core cannot be extraspecial of order thirty-two
and have Sylow relative index two under the ambient rank bound. This stronger
form needs neither the normal four nor its nonnormality in the quotient. -/
public theorem large_core_index_two_false
    {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]
    (hns : ¬ Group.IsSolvable G)
    (hrank : ∀ A : Subgroup G, IsElementaryAbelian 2 A → Nat.card A < 8)
    (S : Sylow 2 G) [IsExtraspecial 2 (pCore 2 (OmegaQuotient S))]
    (hH : Nat.card (pCore 2 (OmegaQuotient S)) = 32)
    (hindex : (pCore 2 (OmegaQuotient S)).relIndex (omegaQuotientSylow S) = 2) :
    False := by
  let H := omegaCorePreimage S
  let : IsExtraspecial 2 H :=
    IsExtraspecial.of_mulEquiv (omegaCorePreimageEquiv S).symm inferInstance
  apply large_core_index_two_false_of_inside_fusion_and_fixed_card hns hrank S hindex
  · intro z t hz hzc hzH _ htH hconj
    exact congrArg Subtype.val (S.eq_of_isConj_in_extraspecial_index_two_of_card_thirty_two
      (elementary_card_lt_eight_of_subgroup hrank (S : Subgroup G)) H
      ((card_omegaCorePreimage S).trans hH) ((index_omegaCorePreimage S).trans hindex)
      ⟨z, hzH⟩ ⟨t, htH⟩ ((orderOf_coe _).symm.trans hz) hzc hconj)
  · intro t ht _
    exact omegaCorePreimage_large_core_involution_centralizer_card_ge_four S hH t ht

end Stellmacher.Recognition.NormalFourCentralOmegaTwo
