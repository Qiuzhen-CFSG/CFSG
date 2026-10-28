module

public import Stellmacher.Recognition.NormalFourNonnormalCoreSetup
public import Theory.GroupTheory.CoprimeInvolutionFusion
public import Theory.GroupTheory.PGroup.OrderSixteenNormalFourCore
public import Theory.GroupTheory.PGroup.OrderSixteenNormalFourOrbit

/-!
# Lifting the involution orbit of the nonnormal four

Conjugacy of Sylow involutions in the actual odd-core quotient lifts to
conjugacy inside the central-omega normalizer. That normalizer fixes the
specified central involution, so this lifting retains the distinction between
the central involution and the other two elements of the normal four.
The order-sixteen quotient core is shown to have a dihedral central factor
and cyclic center of order four, using two distinct normal fours.
The orbit theorem for this core then puts every core involution into the
barred four. Lifting this orbit gives fusion into a noncentral element of
the original four.

Source: Janko–Thompson, Math. Z. 113 (1970), §4, printed pp.389–393;
`refs/original/n-group-global/odd-core-rank-two-source/normal-four-case-split.md`.
-/

namespace Stellmacher.Recognition.NormalFourCentralOmegaTwo

open Subgroup
variable {G : Type*} [Group G] [Finite G]

/-- The barred four is normal in the quotient core, although not in the quotient. -/
public theorem fourImage_normal_in_pCore
    (S : Sylow 2 G) (E : Subgroup S) [E.Normal]
    (hle : fourImage S E ≤ pCore 2 (OmegaQuotient S)) :
    ((fourImage S E).subgroupOf (pCore 2 (OmegaQuotient S))).Normal := by
  apply (normal_subgroupOf_iff_le_normalizer hle).mpr
  have hn := E.le_normalizer_map (omegaQuotientHom S)
  rw [E.normalizer_eq_top, ← MonoidHom.range_eq_map, omegaQuotientHom_range,
    ← fourImage_eq_map] at hn
  exact (pCore_isPGroup.le_sylow_of_normal (omegaQuotientSylow S)).trans hn

/-- The actual order-sixteen core has a dihedral central factor and a cyclic four-center. -/
public theorem omegaQuotient_pCore_dihedral_center_four
    (hN : IsNTwoGroup G)
    (hrank : ∀ A : Subgroup G, IsElementaryAbelian 2 A → Nat.card A < 8)
    (S : Sylow 2 G) (hZ : Nat.card (omega₁ (center S) (p := 2)) = 2)
    (E : Subgroup S) [E.Normal] [IsElementaryAbelian 2 E] (hE : Nat.card E = 4)
    (hunique : ∀ F : Subgroup S, F.Normal → IsElementaryAbelian 2 F →
      Nat.card F = 4 → F = E)
    (hnormal : ¬ (fourImage S E).Normal)
    (hcore : Nat.card (pCore 2 (OmegaQuotient S)) = 16) :
    IsCyclic (center (pCore 2 (OmegaQuotient S))) ∧
      Nat.card (center (pCore 2 (OmegaQuotient S))) = 4 ∧
      ∃ D : Subgroup (pCore 2 (OmegaQuotient S)), D.Normal ∧
        Nonempty (D ≃* DihedralGroup 4) ∧
        D ⊔ center (pCore 2 (OmegaQuotient S)) = ⊤ := by
  have hle := fourImage_le_pCore hN hrank S hZ E hE
  let F := (fourImage S E).subgroupOf (pCore 2 (OmegaQuotient S))
  let : IsElementaryAbelian 2 (fourImage S E) := fourImage_elementary S E
  let : F.Normal := fourImage_normal_in_pCore S E hle
  let : IsElementaryAbelian 2 F := IsElementaryAbelian.subgroupOf hle
  apply dihedral_central_factor_of_order_sixteen_of_no_ambient_normal_four
    (pCore 2 (OmegaQuotient S)) pCore_isPGroup hcore
    (fun U hU => @omegaQuotient_rank _ _ _ hrank S U hU)
    (omegaQuotient_no_normal_four S E hunique hnormal) F
  exact (Nat.card_congr (subgroupOfEquivOfLe hle).toEquiv).trans (fourImage_card S E hE)

omit [Finite G] in
/-- The chosen central involution is fixed by the whole omega normalizer. -/
public theorem central_involution_mem_center_omegaNormalizer
    (S : Sylow 2 G) (hZ : Nat.card (omega₁ (center S) (p := 2)) = 2)
    (z : S) (hz : orderOf z = 2) (hzc : z ∈ center S) :
    inclusion (sylow_le_omegaNormalizer S) z ∈ center (omegaNormalizer S) := by
  let Z := (centralOmega S).subgroupOf (omegaNormalizer S)
  have hc : Nat.card Z = 2 := by
    rw [Nat.card_congr (subgroupOfEquivOfLe
      (le_normalizer : centralOmega S ≤ omegaNormalizer S)).toEquiv,
      card_centralOmega, hZ]
  let : Z.Normal := normal_in_normalizer
  apply central_of_normal_card_two Z hc
  change (z : G) ∈ centralOmega S
  apply mem_map_of_mem
  refine mem_map.mpr ⟨⟨z, hzc⟩, ?_, rfl⟩
  apply Subgroup.subset_closure
  have hp : z ^ 2 = 1 := by simpa only [hz] using pow_orderOf_eq_one z
  simpa using (show (⟨z, hzc⟩ : center S) ^ 2 = 1 from Subtype.ext hp)

/-- Involution conjugacy in the quotient is equivalent to conjugacy in the normalizer. -/
public theorem involution_isConj_omegaNormalizer_iff_quotient
    (S : Sylow 2 G) (x y : S) (hx : orderOf x = 2) (hy : orderOf y = 2) :
    IsConj (inclusion (sylow_le_omegaNormalizer S) x)
      (inclusion (sylow_le_omegaNormalizer S) y) ↔
      IsConj (omegaQuotientHom S x) (omegaQuotientHom S y) := by
  let q := QuotientGroup.mk' (pPrimeCore 2 (omegaNormalizer S))
  rw [omegaQuotientHom_apply, omegaQuotientHom_apply]
  constructor
  · exact q.map_isConj
  · apply q.isConj_of_map_isConj_of_involutions_of_odd_ker
      (QuotientGroup.mk'_surjective _)
      (by simpa only [q, QuotientGroup.ker_mk'] using
        (pPrimeCore_coprime_card (p := 2) (G := omegaNormalizer S)))
    · exact (orderOf_injective _ (inclusion_injective (sylow_le_omegaNormalizer S)) x).trans hx
    · exact (orderOf_injective _ (inclusion_injective (sylow_le_omegaNormalizer S)) y).trans hy

omit [Finite G] in
/-- Normalizer fusion cannot send a different Sylow element to its central involution. -/
public theorem eq_central_involution_of_isConj_omegaNormalizer
    (S : Sylow 2 G) (hZ : Nat.card (omega₁ (center S) (p := 2)) = 2)
    (z : S) (hz : orderOf z = 2) (hzc : z ∈ center S) (t : S)
    (hconj : IsConj (inclusion (sylow_le_omegaNormalizer S) t)
      (inclusion (sylow_le_omegaNormalizer S) z)) : t = z := by
  obtain ⟨g, hg⟩ := isConj_iff.mp hconj.symm
  have hc := mem_center_iff.mp
    (central_involution_mem_center_omegaNormalizer S hZ z hz hzc) g
  have he : inclusion (sylow_le_omegaNormalizer S) z =
      inclusion (sylow_le_omegaNormalizer S) t := by
    simpa only [hc, mul_inv_cancel_right] using hg
  exact inclusion_injective (sylow_le_omegaNormalizer S) he.symm

/-- A quotient orbit meeting the four lifts to a noncentral element of that four.
The conjugator stays in the omega normalizer. -/
public theorem noncentral_four_fusion_of_quotient_orbit
    (S : Sylow 2 G) (hZ : Nat.card (omega₁ (center S) (p := 2)) = 2)
    (E : Subgroup S) [IsElementaryAbelian 2 E]
    (z : E) (hz : orderOf (z : S) = 2) (hzc : (z : S) ∈ center S)
    (t : S) (ht : orderOf t = 2) (htz : t ≠ (z : S))
    (horbit : ∃ v ∈ fourImage S E, IsConj (omegaQuotientHom S t) v) :
    ∃ u : E, u ≠ 1 ∧ u ≠ z ∧
      IsConj (inclusion (sylow_le_omegaNormalizer S) t)
        (inclusion (sylow_le_omegaNormalizer S) (u : S)) := by
  obtain ⟨v, hv, htv⟩ := horbit
  rw [fourImage_eq_map] at hv
  obtain ⟨u, hu, rfl⟩ := hv
  have hu1 : u ≠ 1 := by
    intro he
    subst u
    rw [map_one] at htv
    have ht1 : t = 1 := omegaQuotientHom_injective S
      ((isConj_one_left.mp htv).trans (map_one _).symm)
    simp [ht1] at ht
  have hu2 : orderOf u = 2 := orderOf_eq_prime
    (elemPow_eq_one_of_isElementaryAbelian u hu) hu1
  have hconj := (involution_isConj_omegaNormalizer_iff_quotient S t u ht hu2).mpr htv
  refine ⟨⟨u, hu⟩, fun h => hu1 (congrArg Subtype.val h), ?_, hconj⟩
  intro he
  have huz : u = (z : S) := congrArg Subtype.val he
  rw [huz] at hconj
  exact htz (eq_central_involution_of_isConj_omegaNormalizer S hZ z hz hzc t hconj)

/-- Forgetting the normalizer gives the ambient form required by terminal fusion. -/
public theorem noncentral_four_ambient_fusion_of_quotient_orbit
    (S : Sylow 2 G) (hZ : Nat.card (omega₁ (center S) (p := 2)) = 2)
    (E : Subgroup S) [IsElementaryAbelian 2 E]
    (z : E) (hz : orderOf (z : S) = 2) (hzc : (z : S) ∈ center S)
    (t : S) (ht : orderOf t = 2) (htz : t ≠ (z : S))
    (horbit : ∃ v ∈ fourImage S E, IsConj (omegaQuotientHom S t) v) :
    ∃ u : E, u ≠ 1 ∧ u ≠ z ∧ IsConj (t : G) ((u : S) : G) := by
  obtain ⟨u, hu, huz, hconj⟩ :=
    noncentral_four_fusion_of_quotient_orbit S hZ E z hz hzc t ht htz horbit
  exact ⟨u, hu, huz, (omegaNormalizer S).subtype.map_isConj hconj⟩

/-- Every involution over the order-sixteen core has quotient orbit meeting the four. -/
public theorem core_involution_quotient_orbit
    (hN : IsNTwoGroup G)
    (hrank : ∀ A : Subgroup G, IsElementaryAbelian 2 A → Nat.card A < 8)
    (S : Sylow 2 G) (hZ : Nat.card (omega₁ (center S) (p := 2)) = 2)
    (E : Subgroup S) [E.Normal] [IsElementaryAbelian 2 E] (hE : Nat.card E = 4)
    (hunique : ∀ F : Subgroup S, F.Normal → IsElementaryAbelian 2 F →
      Nat.card F = 4 → F = E)
    (hnormal : ¬ (fourImage S E).Normal)
    (hcore : Nat.card (pCore 2 (OmegaQuotient S)) = 16)
    (t : S) (ht : orderOf t = 2) (htcore : t ∈ omegaCorePreimage S) :
    ∃ v ∈ fourImage S E, IsConj (omegaQuotientHom S t) v := by
  have hle := fourImage_le_pCore hN hrank S hZ E hE
  let F := (fourImage S E).subgroupOf (pCore 2 (OmegaQuotient S))
  let : IsElementaryAbelian 2 (fourImage S E) := fourImage_elementary S E
  let : F.Normal := fourImage_normal_in_pCore S E hle
  let : IsElementaryAbelian 2 F := IsElementaryAbelian.subgroupOf hle
  have hF : Nat.card F = 4 :=
    (Nat.card_congr (subgroupOfEquivOfLe hle).toEquiv).trans (fourImage_card S E hE)
  let t' : pCore 2 (OmegaQuotient S) := ⟨omegaQuotientHom S t, htcore⟩
  have ht' : orderOf t' = 2 := by
    rw [← Subgroup.orderOf_coe t']
    exact (orderOf_injective _ (omegaQuotientHom_injective S) t).trans ht
  obtain ⟨u, hu⟩ := exists_isConj_mem_normal_four_of_order_sixteen
    (pCore 2 (OmegaQuotient S)) pCore_isPGroup hcore
    (fun U hU => @omegaQuotient_rank _ _ _ hrank S U hU)
    (omegaQuotient_no_normal_four S E hunique hnormal) F hF t' ht'
  exact ⟨((u : pCore 2 (OmegaQuotient S)) : OmegaQuotient S), u.property, hu⟩

/-- A noncentral core involution fuses into the noncentral part of the normal four,
with conjugator in the omega normalizer. -/
public theorem noncentral_core_involution_four_fusion
    (hN : IsNTwoGroup G)
    (hrank : ∀ A : Subgroup G, IsElementaryAbelian 2 A → Nat.card A < 8)
    (S : Sylow 2 G) (hZ : Nat.card (omega₁ (center S) (p := 2)) = 2)
    (E : Subgroup S) [E.Normal] [IsElementaryAbelian 2 E] (hE : Nat.card E = 4)
    (hunique : ∀ F : Subgroup S, F.Normal → IsElementaryAbelian 2 F →
      Nat.card F = 4 → F = E)
    (hnormal : ¬ (fourImage S E).Normal)
    (hcore : Nat.card (pCore 2 (OmegaQuotient S)) = 16)
    (z : E) (hz : orderOf (z : S) = 2) (hzc : (z : S) ∈ center S)
    (t : S) (ht : orderOf t = 2) (htz : t ≠ (z : S))
    (htcore : t ∈ omegaCorePreimage S) :
    ∃ u : E, u ≠ 1 ∧ u ≠ z ∧
      IsConj (inclusion (sylow_le_omegaNormalizer S) t)
        (inclusion (sylow_le_omegaNormalizer S) (u : S)) := by
  exact noncentral_four_fusion_of_quotient_orbit S hZ E z hz hzc t ht htz
    (core_involution_quotient_orbit hN hrank S hZ E hE hunique hnormal hcore t ht htcore)

/-- The ambient fusion form of the inside-core involution orbit calculation. -/
public theorem noncentral_core_involution_four_ambient_fusion
    (hN : IsNTwoGroup G)
    (hrank : ∀ A : Subgroup G, IsElementaryAbelian 2 A → Nat.card A < 8)
    (S : Sylow 2 G) (hZ : Nat.card (omega₁ (center S) (p := 2)) = 2)
    (E : Subgroup S) [E.Normal] [IsElementaryAbelian 2 E] (hE : Nat.card E = 4)
    (hunique : ∀ F : Subgroup S, F.Normal → IsElementaryAbelian 2 F →
      Nat.card F = 4 → F = E)
    (hnormal : ¬ (fourImage S E).Normal)
    (hcore : Nat.card (pCore 2 (OmegaQuotient S)) = 16)
    (z : E) (hz : orderOf (z : S) = 2) (hzc : (z : S) ∈ center S)
    (t : S) (ht : orderOf t = 2) (htz : t ≠ (z : S))
    (htcore : t ∈ omegaCorePreimage S) :
    ∃ u : E, u ≠ 1 ∧ u ≠ z ∧ IsConj (t : G) ((u : S) : G) := by
  obtain ⟨u, hu, huz, hconj⟩ := noncentral_core_involution_four_fusion
    hN hrank S hZ E hE hunique hnormal hcore z hz hzc t ht htz htcore
  exact ⟨u, hu, huz, (omegaNormalizer S).subtype.map_isConj hconj⟩

end Stellmacher.Recognition.NormalFourCentralOmegaTwo
