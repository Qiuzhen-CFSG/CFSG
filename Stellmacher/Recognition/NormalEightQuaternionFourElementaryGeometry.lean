module

public import Stellmacher.Recognition.NormalEightQuaternionFourElementarySetup
public import Stellmacher.Recognition.NormalEightQuaternionHigherIndexSetup
public import Theory.GroupTheory.QuaternionElementaryFixedFour
public import Theory.GroupTheory.IndexFourInvolutionTransfer
public import Theory.GroupTheory.PGroup.CyclicFourFixedCoreDerived

/-!
# The fixed four and the outside quaternion involution coset

The elementary fixed-core bound rules out factor swapping and mixed quaternion
actions. The remaining action has fixed order four and one core orbit of
outside-coset involutions. Consequently its centralizer covers the core
quotient. Since the extraspecial core has central commutators, this supplement
makes the fixed four normal in the Sylow subgroup, identifying it with the
unique normal four.

Source: Janko–Thompson, Math. Z. 113 (1970), §4 case (b)(ii), printed p.391.
-/

open Subgroup
open Stellmacher.Recognition.NormalFourCentralOmegaTwo
namespace Stellmacher.Recognition.NormalEightNonnormalImage
variable {G : Type*} [Group G] [Finite G]

/-- The elementary fixed-core branch has a fixed four and a single orbit
of involutions in the outside coset. -/
public theorem quaternion_four_elementary_fixed_card_and_coset
    (hN : IsNTwoGroup G) (S : Sylow 2 G)
    (hZ : Nat.card (omega₁ (center S) (p := 2)) = 2)
    (B C : Subgroup (pCore 2 (OmegaQuotient S)))
    (hB : Nonempty (B ≃* QuaternionGroup 2)) (hC : Nonempty (C ≃* QuaternionGroup 2))
    (hjoin : B ⊔ C = ⊤) (hinter : Nat.card (B ⊓ C : Subgroup _) = 2)
    (hcomm : ∀ b ∈ B, ∀ c ∈ C, b*c=c*b)
    (t : S) (ht : orderOf t = 2) (hout : t ∉ omegaCorePreimage S)
    (hfixed : IsElementaryAbelian 2 ((omegaCorePreimage S).subgroupOf
      (centralizer ({t} : Set S))))
    (hfixed_card : Nat.card ((omegaCorePreimage S).subgroupOf
      (centralizer ({t} : Set S))) ≤ 4) :
    IsElementaryAbelian 2 (omegaCorePreimage S ⊓ centralizer ({t} : Set S) : Subgroup S) ∧
      Nat.card (omegaCorePreimage S ⊓ centralizer ({t} : Set S) : Subgroup S) = 4 ∧
      (∀ u : S, orderOf u = 2 → u * t⁻¹ ∈ omegaCorePreimage S →
        ∃ h : S, h ∈ omegaCorePreimage S ∧ h * t * h⁻¹ = u) := by
  have hself : centralizer (omegaCorePreimage S : Set S) ≤ omegaCorePreimage S := by
    intro s hs
    apply omegaQuotient_centralizer_pCore_le hN S hZ
    intro x hx
    rw [← omegaCorePreimage_map S] at hx
    obtain ⟨k, hk, rfl⟩ := hx
    simpa only [map_mul] using congrArg (omegaQuotientHom S) (hs k hk)
  exact quaternion_elementary_fixed_four_and_coset_orbit (omegaCorePreimage S)
    (omegaCorePreimageEquiv S) hself B C hB hC hjoin hinter hcomm
    t ht hout hfixed hfixed_card

/-- Coset transitivity makes the fixed four normal, so uniqueness identifies
it with the distinguished normal four. -/
public theorem quaternion_four_elementary_fixed_eq_and_coset
    (hN : IsNTwoGroup G) (S : Sylow 2 G)
    (hZ : Nat.card (omega₁ (center S) (p := 2)) = 2)
    (W : Subgroup S)
    (hunique : ∀ F : Subgroup S, F.Normal → IsElementaryAbelian 2 F → Nat.card F = 4 → F = W)
    [IsExtraspecial 2 (pCore 2 (OmegaQuotient S))]
    (B C : Subgroup (pCore 2 (OmegaQuotient S)))
    (hB : Nonempty (B ≃* QuaternionGroup 2)) (hC : Nonempty (C ≃* QuaternionGroup 2))
    (hjoin : B ⊔ C = ⊤) (hinter : Nat.card (B ⊓ C : Subgroup _) = 2)
    (hcomm : ∀ b ∈ B, ∀ c ∈ C, b*c=c*b)
    (t : S) (ht : orderOf t = 2) (hout : t ∉ omegaCorePreimage S)
    (hindex : (omegaCorePreimage S).index = 4)
    (hfixed : IsElementaryAbelian 2 ((omegaCorePreimage S).subgroupOf
      (centralizer ({t} : Set S))))
    (hfixed_card : Nat.card ((omegaCorePreimage S).subgroupOf
      (centralizer ({t} : Set S))) ≤ 4) :
    omegaCorePreimage S ⊓ centralizer ({t} : Set S) = W ∧
      (∀ u : S, orderOf u = 2 → u * t⁻¹ ∈ omegaCorePreimage S →
        ∃ h : S, h ∈ omegaCorePreimage S ∧ h * t * h⁻¹ = u) := by
  obtain ⟨helem, hcard, horbit⟩ := quaternion_four_elementary_fixed_card_and_coset
    hN S hZ B C hB hC hjoin hinter hcomm t ht hout hfixed hfixed_card
  have hsup := sup_centralizer_eq_top_of_index_four_coset_involutions
    (omegaCorePreimage S) hindex t ht horbit
  let P := omegaCorePreimage S
  let : IsExtraspecial 2 P :=
    IsExtraspecial.of_mulEquiv (omegaCorePreimageEquiv S).symm inferInstance
  have hclass : ⁅P,P⁆ ≤ center S := by
    rw [← map_subtype_commutator]
    apply (map_mono (IsExtraspecial.quotient_elementary_abelian 2 P).commutator_le_center_of_central_quotient).trans
    exact central_of_normal_card_two ((center P).map P.subtype) (by
      rw [card_map_of_injective P.subtype_injective, IsExtraspecial.center_order_p 2 P])
  exact ⟨hunique _ (fixed_core_normal_of_centralizer_supplement P t
    (by simpa only [sup_comm] using hsup) hclass) helem hcard, horbit⟩

/-- The order-nine action on the actual quaternion core carries every
noncentral involution into the normal four; the odd kernel lifts this fusion. -/
public theorem quaternion_four_core_involution_cover
    (hN : IsNTwoGroup G) (S : Sylow 2 G)
    (hZ : Nat.card (omega₁ (center S) (p := 2)) = 2)
    (hno : ¬ ∃ F : Subgroup S, F.Normal ∧ IsElementaryAbelian 2 F ∧ 8 ≤ Nat.card F)
    (W : Subgroup S) [W.Normal] [IsElementaryAbelian 2 W] (hW : Nat.card W = 4)
    [IsExtraspecial 2 (pCore 2 (OmegaQuotient S))]
    (hH : Nat.card (pCore 2 (OmegaQuotient S)) = 32)
    (B C : Subgroup (pCore 2 (OmegaQuotient S)))
    (hB : Nonempty (B ≃* QuaternionGroup 2)) (hC : Nonempty (C ≃* QuaternionGroup 2))
    (hjoin : B ⊔ C = ⊤) (hinter : Nat.card (B ⊓ C : Subgroup _) = 2)
    (hcomm : ∀ b ∈ B, ∀ c ∈ C, b*c=c*b)
    (z : S) (hz : orderOf z = 2) (hzc : z ∈ center S)
    (hindex : 4 ≤ (omegaCorePreimage S).index) :
    ∀ u : S, u ∈ omegaCorePreimage S → orderOf u = 2 →
      ∃ w : S, w ∈ W ∧ IsConj (u : G) (w : G) := by
  let P := omegaCorePreimage S
  let e := omegaCorePreimageEquiv S
  let : IsExtraspecial 2 P := IsExtraspecial.of_mulEquiv e.symm inferInstance
  have hWP : W ≤ P := four_le_omegaCorePreimage hN S hZ W hW hno
  have hzW : z ∈ W := omega_one_center_le_normal_four_of_no_normal_eight hno W hW
    ⟨⟨z, hzc⟩, subset_closure (by
      apply Subtype.ext
      change z ^ (2 ^ 1) = 1
      simpa only [pow_one, hz] using pow_orderOf_eq_one z), rfl⟩
  let zP : P := ⟨z, hWP hzW⟩
  have hzP : orderOf zP = 2 := (orderOf_coe zP).symm.trans hz
  have hzPC : zP ∈ center P := mem_center_iff.mpr (fun x =>
    Subtype.ext (mem_center_iff.mp hzc (x : S)))
  have hline : zpowers zP = center P := by
    apply eq_of_le_of_card_ge (zpowers_le.mpr hzPC)
    rw [Nat.card_zpowers, hzP, IsExtraspecial.center_order_p 2 P]
  have hCW : center P ≤ W.subgroupOf P := by
    rw [← hline]
    exact zpowers_le.mpr hzW
  have hnot : ¬ W.subgroupOf P ≤ center P := by
    intro h
    have hc := card_le_of_le h
    rw [Nat.card_congr (subgroupOfEquivOfLe hWP).toEquiv, hW,
      IsExtraspecial.center_order_p 2 P] at hc
    omega
  obtain ⟨y, hyW, hyC⟩ := SetLike.not_le_iff_exists.mp hnot
  have hyne : y ≠ 1 := fun hh => hyC (hh ▸ (center P).one_mem)
  have hy : orderOf (y : S) = 2 := orderOf_eq_prime
    (elemPow_eq_one_of_isElementaryAbelian (y : S) hyW)
    (fun hh => hyne (Subtype.ext hh))
  let yQ : pCore 2 (OmegaQuotient S) := ⟨omegaQuotientHom S y, y.property⟩
  have hny : yQ ∉ center (pCore 2 (OmegaQuotient S)) := by
    intro h
    apply hyC
    apply mem_center_iff.mpr
    intro x
    apply Subtype.ext
    apply omegaQuotientHom_injective S
    have hh := congrArg Subtype.val (mem_center_iff.mp h
      (⟨omegaQuotientHom S x, x.property⟩ : pCore 2 (OmegaQuotient S)))
    simpa only [coe_mul, map_mul] using hh
  obtain ⟨U, hU⟩ := quaternion_core_exists_nine_subgroup
    hN S hZ hH B C hB hC hjoin hinter hcomm hindex
  intro u huP hu
  let x : P := ⟨u, huP⟩
  by_cases hxC : x ∈ center P
  · exact ⟨u, hCW hxC, IsConj.refl _⟩
  let xQ : pCore 2 (OmegaQuotient S) := ⟨omegaQuotientHom S u, huP⟩
  have hnx : xQ ∉ center (pCore 2 (OmegaQuotient S)) := by
    intro h
    apply hxC
    apply mem_center_iff.mpr
    intro v
    apply Subtype.ext
    apply omegaQuotientHom_injective S
    have hh := congrArg Subtype.val (mem_center_iff.mp h
      (⟨omegaQuotientHom S v, v.property⟩ : pCore 2 (OmegaQuotient S)))
    simpa only [coe_mul, map_mul] using hh
  refine ⟨y, hyW, isConj_of_omegaQuotient_isConj S u y hu hy ?_⟩
  exact quaternion_core_noncentral_involution_conjugacy hN S hZ hH
    B C hB hC hjoin hinter hcomm U hU xQ yQ
    ((orderOf_coe xQ).symm.trans
      ((orderOf_injective _ (omegaQuotientHom_injective S) u).trans hu)) hnx
    ((orderOf_coe yQ).symm.trans
      ((orderOf_injective _ (omegaQuotientHom_injective S) y).trans hy)) hny

end Stellmacher.Recognition.NormalEightNonnormalImage
