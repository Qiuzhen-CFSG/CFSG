module

public import CFSG.Quasithin.Chapter14.Section04.LargerDimension.Orthogonal.Defs
public import Theory.GroupTheory.IrreducibleCentralInvolutionLift
public import Theory.GroupTheory.Commutator.ElementaryQuotientIndexTwoQuadratic
public import Theory.ElementaryAbelian.ExtraspecialNormalCommutator
public import Theory.GroupTheory.NormalizingInvolutionCard
public import Theory.ElementaryAbelian.Join

/-!
# The elementary order-64 lift in the orthogonal branch

For the literal moved image of U in U/Z(U), rank four gives |[U,i]|=32:
a nontrivial normal subgroup of the extraspecial U contains its center.
Quadraticity modulo that center and irreducibility of the moved section
force i to centralize [U,i]. The involution-lift theorem proves that this
subgroup is elementary. Adjoining the external involution i doubles its
order. The actual group K₀U normalizes the resulting lift.

The hypotheses specify the source center, involution, normalizing action,
and irreducibility as the interval of invariant subgroups above the center.
No elementary-lift conclusion is an input.

Source: Aschbacher–Smith, Lemma 14.4.9, printed p.1010.
-/

public section
open Subgroup
open scoped commutatorElement IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section04.LargerDimension.Orthogonal
variable {G : Type*} [Group G] [Finite G]


theorem liftBase_eq_commutator_and_card
    (U : Subgroup G) [IsExtraspecial 2 U] (z i : G)
    (hZ : (center U).map U.subtype = zpowers z)
    (hiU : i ∈ normalizer (U : Set G))
    (hmoved : Nat.card (((⁅U,zpowers i⁆).subgroupOf U).map
      (QuotientGroup.mk' (center U))) = 16) :
    liftBase U z i = ⁅U,zpowers i⁆ ∧ Nat.card (liftBase U z i) = 32 := by
  let B := ⁅U,zpowers i⁆
  let B₀ := B.subgroupOf U
  have hBU : B ≤ U := le_normalizer_iff_commutator_le_left.mp (zpowers_le.mpr hiU)
  let : B₀.Normal := normal_subgroupOf_of_le_normalizer (normalizer_commutator_ge_left _ _)
  have hBne : B₀ ≠ ⊥ := by
    intro he
    change Nat.card (B₀.map (QuotientGroup.mk' (center U))) = 16 at hmoved
    rw [he, Subgroup.map_bot, Nat.card_unique] at hmoved
    omega
  have hZB : center U ≤ B₀ := extraspecial_center_le_of_normal_ne_bot B₀ hBne
  have hzB : zpowers z ≤ B := by
    rw [← hZ, ← map_subgroupOf_eq_of_le hBU]
    exact map_mono hZB
  have he : liftBase U z i = B := sup_eq_left.mpr hzB
  refine ⟨he, ?_⟩
  have hidx : (center U).relIndex B₀ = 16 := by
    simpa only [QuotientGroup.ker_mk'] using
      (relIndex_ker B₀ (QuotientGroup.mk' (center U))).trans hmoved
  have hZcard : Nat.card ((center U).subgroupOf B₀) = 2 := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hZB).toEquiv]
    exact IsExtraspecial.center_order_p 2 U
  have hm := ((center U).subgroupOf B₀).card_mul_index
  rw [hZcard, show ((center U).subgroupOf B₀).index = 16 from hidx] at hm
  rw [he, ← Nat.card_congr (subgroupOfEquivOfLe hBU).toEquiv]
  exact hm.symm

theorem centralizerLift_elementary_and_card
    (U K : Subgroup G) [IsExtraspecial 2 U] (z i : G)
    (hz : orderOf z = 2) (hi : orderOf i = 2)
    (hZ : (center U).map U.subtype = zpowers z)
    (hiU : i ∈ normalizer (U : Set G)) (hiz : i ∈ centralizer ({z} : Set G))
    (hout : i ∉ U)
    (hKU : K ≤ normalizer (U : Set G))
    (hKi : K ≤ centralizer ({i} : Set G))
    (hmoved : Nat.card (((⁅U,zpowers i⁆).subgroupOf U).map
      (QuotientGroup.mk' (center U))) = 16)
    (hirr : ∀ E : Subgroup G, zpowers z ≤ E → E ≤ liftBase U z i →
      K ≤ normalizer (E : Set G) → E = zpowers z ∨ E = liftBase U z i) :
    IsElementaryAbelian 2 (centralizerLift U z i) ∧
      Nat.card (centralizerLift U z i) = 64 ∧
      IsElementaryAbelian 2 (liftBase U z i) ∧ Nat.card (liftBase U z i) = 32 := by
  obtain ⟨hAB, hAcard⟩ := liftBase_eq_commutator_and_card U z i hZ hiU hmoved
  let B := ⁅U,zpowers i⁆
  have hBU : B ≤ U := le_normalizer_iff_commutator_le_left.mp (zpowers_le.mpr hiU)
  have hzB : zpowers z ≤ B := by
    change zpowers z ≤ ⁅U,zpowers i⁆
    rw [← hAB]
    exact le_sup_right
  have hzU : zpowers z ≤ U := hzB.trans hBU
  have hZZ : (zpowers z).subgroupOf U = center U := by
    apply map_injective U.subtype_injective
    rw [map_subgroupOf_eq_of_le hzU, hZ]
  have hzCU : zpowers z ≤ centralizer (U : Set G) := by
    rw [← hZ]
    rintro _ ⟨a, ha, rfl⟩ u hu
    exact congrArg Subtype.val (mem_center_iff.mp ha (⟨u,hu⟩ : U))
  have hZi : zpowers z ≤ centralizer ({i} : Set G) := by
    apply zpowers_le.mpr
    exact mem_centralizer_singleton_iff.mpr (mem_centralizer_singleton_iff.mp hiz).symm
  have hiZ : zpowers i ≤ normalizer (zpowers z : Set G) := by
    apply (le_centralizer_iff.mp (show zpowers z ≤ centralizer (zpowers i : Set G) by
      simpa only [zpowers_eq_closure, centralizer_closure] using hZi)).trans
    exact _root_.centralizer_le_normalizer _
  have hN : ((zpowers z).subgroupOf U).Normal := hZZ ▸ inferInstance
  have helem : let _ := hN; IsElementaryAbelian 2 (U ⧸ (zpowers z).subgroupOf U) := by
    generalize he : (zpowers z).subgroupOf U = Z at hZZ hN ⊢
    clear he
    subst Z
    exact IsExtraspecial.quotient_elementary_abelian 2 U
  have hdouble : ⁅B,zpowers i⁆ ≤ zpowers z := by
    apply commutator_commutator_le_of_elementary_quotient_index_two U (zpowers z)
      ⊥ (zpowers i) hzU (zpowers_le.mpr hiU) hiZ hN helem bot_le
    · rw [relIndex_bot_left, Nat.card_zpowers, hi]
    · rw [commutator_bot_right]
      exact bot_le
  have hKB : K ≤ normalizer (B : Set G) := by
    intro k hk
    apply mem_normalizer_iff_map_conj_eq.mpr
    rw [map_commutator, mem_normalizer_iff_map_conj_eq.mp (hKU hk), MonoidHom.map_zpowers]
    congr 2
    change k * i * k⁻¹ = i
    rw [mem_centralizer_singleton_iff.mp (hKi hk)]
    group
  have hfixed : B ≤ centralizer ({i} : Set G) := by
    apply centralizes_of_irreducible_section B (zpowers z) K i hzB
      (hzCU.trans (centralizer_le hBU)) hZi hdouble hKB hKi
    · rw [Nat.card_zpowers, hz, show Nat.card B = 32 by simpa only [hAB] using hAcard]
      decide
    · simpa only [hAB] using hirr
  have hUU : ⁅U,U⁆ ≤ zpowers z := by
    have hh := map_mono (f := U.subtype)
      (IsExtraspecial.quotient_elementary_abelian 2 U).commutator_le_center_of_central_quotient
    simpa only [map_subtype_commutator, hZ] using hh
  have hi2 : i ^ 2 = 1 := by rw [← hi]; exact pow_orderOf_eq_one i
  let : IsElementaryAbelian 2 B :=
    elementary_commutator_of_fixed U (zpowers z) i hi2 hBU hUU hZi hfixed
  let : IsElementaryAbelian 2 (zpowers i) := IsElementaryAbelian.zpowers_of_pow_eq_one hi2
  have hiB : zpowers i ≤ centralizer (B : Set G) := by
    apply le_centralizer_iff.mp
    simpa only [zpowers_eq_closure, centralizer_closure] using hfixed
  have hD : centralizerLift U z i = B ⊔ zpowers i := by
    exact sup_eq_left.mpr (hzB.trans le_sup_left)
  refine ⟨hD ▸ IsElementaryAbelian.sup_of_le_centralizer hiB, ?_, hAB ▸ inferInstance, hAcard⟩
  rw [hD, card_sup_zpowers_of_normalizing_involution B i hi2 (fun h => hout (hBU h))
    (_root_.centralizer_le_normalizer _ (hiB (mem_zpowers i))), show Nat.card B = 32 by simpa only [hAB] using hAcard]

theorem lift_normalized_by_residual_join_core
    (U K : Subgroup G) [IsExtraspecial 2 U] (z i : G)
    (hZ : (center U).map U.subtype = zpowers z)
    (hiU : i ∈ normalizer (U : Set G))
    (hKU : K ≤ normalizer (U : Set G))
    (hKi : K ≤ centralizer ({i} : Set G))
    (hmoved : Nat.card (((⁅U,zpowers i⁆).subgroupOf U).map
      (QuotientGroup.mk' (center U))) = 16) :
    K ⊔ U ≤ normalizer (centralizerLift U z i : Set G) := by
  obtain ⟨hAB, _⟩ := liftBase_eq_commutator_and_card U z i hZ hiU hmoved
  let B := ⁅U,zpowers i⁆
  have hzB : zpowers z ≤ B := by
    change zpowers z ≤ ⁅U,zpowers i⁆
    rw [← hAB]
    exact le_sup_right
  have hD : centralizerLift U z i = B ⊔ zpowers i :=
    sup_eq_left.mpr (hzB.trans le_sup_left)
  rw [hD]
  apply sup_le
  · intro k hk
    apply mem_normalizer_iff_map_conj_eq.mpr
    rw [Subgroup.map_sup, show B.map (MulAut.conj k : G →* G) = B by
      dsimp only [B]
      rw [map_commutator, mem_normalizer_iff_map_conj_eq.mp (hKU hk),
        MonoidHom.map_zpowers]
      congr 2
      change k * i * k⁻¹ = i
      rw [mem_centralizer_singleton_iff.mp (hKi hk)]
      group, MonoidHom.map_zpowers]
    congr 2
    change k * i * k⁻¹ = i
    rw [mem_centralizer_singleton_iff.mp (hKi hk)]
    group
  · apply le_normalizer_iff.mpr
    intro u hu d hd
    have hmap : (B ⊔ zpowers i).map (MulAut.conj u : G →* G) ≤ B ⊔ zpowers i := by
      rw [Subgroup.map_sup,
        show B.map (MulAut.conj u : G →* G) = B from
          mem_normalizer_iff_map_conj_eq.mp (normalizer_commutator_ge_left U (zpowers i) hu),
        MonoidHom.map_zpowers]
      apply sup_le le_sup_left
      apply zpowers_le.mpr
      change u * i * u⁻¹ ∈ B ⊔ zpowers i
      have he : u * i * u⁻¹ = ⁅u,i⁆ * i := by simp [commutatorElement_def, mul_assoc]
      rw [he]
      exact mul_mem_sup (commutator_mem_commutator hu (mem_zpowers i)) (mem_zpowers i)
    exact hmap (mem_map_of_mem (MulAut.conj u : G →* G) hd)


end CFSG.Quasithin.Chapter14.Section04.LargerDimension.Orthogonal
