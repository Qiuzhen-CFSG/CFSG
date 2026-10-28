module
public import CFSG.Quasithin.Chapter13.Section03.SourceCompletion.OriginalPlaneCentralizers.Inspection.CubicPlacement
public import CFSG.Quasithin.Chapter12.Section02.Preliminaries.NormalizerSourceAt
public import CFSG.Quasithin.Chapter12.Section02.SourceApplications.At
public import CFSG.Quasithin.Chapter13.Section03.SourceCompletion.At.OriginalPlaneCentralizers.Inspection.Normality

/-!
# Original unitary source argument at the same ambient group and Sylow subgroup

This is the ambient-local specialization of `OriginalPlaneCentralizers.Inspection.CubicPlacement`.
Its proof retains the original subgroups, actions, relative Sylow placement,
and quotient maps. Only the earlier 12.2.2 and 12.2.13 inputs are restricted
to the fixed G,T. The universal public API remains in the imported module.
The source argument and reference are recorded there; no additional local
classification or normalizer premise is introduced by this specialization.
-/

public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative MatrixGroups
namespace CFSG.Quasithin.Chapter13.Section03.SourceCompletion.At.OriginalPlaneCentralizers
open CFSG.Quasithin.Chapter13.Section03.SourceCompletion.OriginalPlaneCentralizers
open ChapterE Atlas.G2.Natural.BinaryNondegeneratePlane
open Representation.BinaryOffender

private theorem second_derived : secondCubic ∈ commutator (Atlas.G2.Model K) := by
  have he : cubicCommutator.val = secondCubic := by
    apply rho_injective
    apply LinearMap.ext
    intro v
    rw [cubicCommutator_action, secondCubic_action]
  exact he ▸ cubicCommutator.property

private theorem cubic_nine :
    let E := zpowers cubic ⊔ zpowers secondCubic
    IsElementaryAbelian 3 E ∧ Nat.card E = 9 ∧
      E ≤ commutator (Atlas.G2.Model K) ∧
      E ≤ subspaceStabilizer rho plane ∧
      E ⊓ subspaceKernel rho plane ⊤ = zpowers cubic := by
  let C := zpowers cubic
  let P := subspaceKernel rho plane ⊤
  have hCP : C ≤ P := zpowers_le.mpr ⟨mem_top _, cubic_fixes_plane⟩
  have hsecond : secondCubic ∉ P := by
    intro h
    have hh := h.2 firstVector (by rw [mem_plane]; decide)
    have h0 := congrFun hh 0
    rw [secondCubic_action] at h0
    exact zero_ne_one (show (0 : K) = 1 from h0)
  let : IsElementaryAbelian 3 C := IsElementaryAbelian.zpowers_of_pow_eq_one cubic_cubed
  have hC : Nat.card C = 3 := (Nat.card_zpowers cubic).trans orderOf_cubic
  have hfix : C ≤ centralizer ({secondCubic} : Set (Atlas.G2.Model K)) :=
    zpowers_le.mpr (mem_centralizer_singleton_iff.mpr cubics_commute.eq)
  obtain ⟨hE,hcard⟩ := IsElementaryAbelian.fixed_join_card (n := 1) C secondCubic
    orderOf_secondCubic (C.disjoint_zpowers_of_prime_order_not_mem secondCubic
      orderOf_secondCubic (fun h => hsecond (hCP h))) hfix (by simpa using hC)
  let E := C ⊔ zpowers secondCubic
  let : IsElementaryAbelian 3 E := hE
  have hcE : Nat.card E = 9 := hcard
  have hES : E ≤ subspaceStabilizer rho plane := by
    apply sup_le
    · apply zpowers_le.mpr
      rw [←productHom_range]
      exact ⟨(cubicMatrix,1), by simp [cubic]⟩
    · apply zpowers_le.mpr
      rw [←productHom_range]
      exact ⟨(1,cubicMatrix), by simp [secondCubic]⟩
  refine ⟨hE,hcE,sup_le (zpowers_le.mpr cubic_mem_derived)
    (zpowers_le.mpr second_derived),hES,?_⟩
  have hP : Nat.card P = 6 := by
    obtain ⟨e⟩ := pointwise_plane_equiv_s3
    rw [Nat.card_congr e.toEquiv,Nat.card_eq_fintype_card,Fintype.card_perm]
    decide
  have hd9 : Nat.card (E ⊓ P : Subgroup (Atlas.G2.Model K)) ∣ 9 :=
    hcE ▸ card_dvd_of_le inf_le_left
  have hd6 : Nat.card (E ⊓ P : Subgroup (Atlas.G2.Model K)) ∣ 6 :=
    hP ▸ card_dvd_of_le inf_le_right
  have hd3 : Nat.card (E ⊓ P : Subgroup (Atlas.G2.Model K)) ∣ 3 :=
    Nat.dvd_gcd hd9 hd6
  apply (eq_of_le_of_card_ge (le_inf le_sup_left hCP) ?_).symm
  rw [hC]
  exact Nat.le_of_dvd (by decide) hd3

variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  [IsElementaryAbelian 2 V]

omit [Finite G] in
private theorem normalizes_of_plane_action (d : MarkedPlane V)
    (n : normalizer (V : Set G))
    (hn : d.chart (V.normalizerMonoidHom.rangeRestrict n) ∈ subspaceStabilizer rho plane) :
    n.val ∈ normalizer (d.A : Set G) := by
  rw [mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    let v : Additive V := Additive.ofMul ⟨x,d.le_module hx⟩
    apply (mem_pointCoordinateSubspace d.coordinates d.A
      (automizerRepresentation V (V.normalizerMonoidHom.rangeRestrict n) v)).mp
    rw [d.plane_space,d.equivariant]
    exact (hn _).mpr (d.plane_space ▸
      (mem_pointCoordinateSubspace d.coordinates d.A v).mpr hx)
  · intro hx
    have hxV : x ∈ V := (mem_normalizer_iff.mp n.property x).mpr (d.le_module hx)
    let v : Additive V := Additive.ofMul ⟨x,hxV⟩
    have hv : d.coordinates (automizerRepresentation V
        (V.normalizerMonoidHom.rangeRestrict n) v) ∈ plane := d.plane_space ▸
      (mem_pointCoordinateSubspace d.coordinates d.A _).mpr hx
    rw [d.equivariant] at hv
    exact (mem_pointCoordinateSubspace d.coordinates d.A v).mp
      (d.plane_space.symm ▸ (hn _).mp hv)

/-- The specified cubic lifts with order three inside both the original
component and L. -/
theorem Context.component_marked_cubic_order_three (s : Context T L V) (d : MarkedPlane V)
    (J : Subgroup G) (j : LocalData T L d J) :
    ∃ n : normalizer (V : Set G), n.val ∈ J ∧ n.val ∈ L ∧ orderOf n.val = 3 ∧
      d.chart (V.normalizerMonoidHom.rangeRestrict n) = cubic := by
  let f : L →* Atlas.G2.Model K := d.chart.comp
    (V.normalizerMonoidHom.rangeRestrict.comp (inclusion s.chosen.normalizes))
  have hk : f.ker = pCore 2 L := s.component_action_ker d
  have hcop : Nat.Coprime 3 (Nat.card f.ker) := by
    rw [hk]
    obtain ⟨n,hn⟩ := (pCore_isPGroup (p := 2) (G := L)).exists_card_eq
    rw [hn]
    exact (by decide : Nat.Coprime 3 2).pow_right n
  have hfr : f.range = commutator (Atlas.G2.Model K) := by
    let : Group.IsPerfect L := Chapter1.mem_L_isPerfect s.maximal.1
    rw [←component_actor_image s.chosen.normalizes s.actor d.chart d.coordinates d.equivariant]
    ext x
    constructor
    · rintro ⟨l,rfl⟩
      exact ⟨_,⟨inclusion s.chosen.normalizes l,l.property,rfl⟩,rfl⟩
    · rintro ⟨a,⟨l,hl,rfl⟩,rfl⟩
      exact ⟨⟨l.val,hl⟩,rfl⟩
  let E := zpowers cubic ⊔ zpowers secondCubic
  obtain ⟨hE,hcard,hED,hES,hEP⟩ := cubic_nine
  let : IsElementaryAbelian 3 E := hE
  have hER : E ≤ f.range := hED.trans_eq hfr.symm
  let ER := E.subgroupOf f.range
  let : IsElementaryAbelian 3 ER := IsElementaryAbelian.of_injective
    (subgroupOfEquivOfLe hER).toMonoidHom (subgroupOfEquivOfLe hER).injective
  obtain ⟨A,hA,hm,hc⟩ := exists_elementaryAbelian_map_eq_of_surjective_coprime
    f.rangeRestrict f.rangeRestrict_surjective (by rwa [MonoidHom.ker_rangeRestrict]) ER
  let : IsElementaryAbelian 3 A := hA
  have hAf : A.map f = E := by
    have hh := congrArg (map f.range.subtype) hm
    rwa [map_map,MonoidHom.subtype_comp_rangeRestrict,map_subgroupOf_eq_of_le hER] at hh
  have himage (a : L) (ha : a ∈ A) : f a ∈ E := by
    rw [←hAf]
    exact mem_map_of_mem f ha
  have hcA : Nat.card A = 9 := hc.trans
    ((Nat.card_congr (subgroupOfEquivOfLe hER).toEquiv).trans hcard)
  let N := normalizer (d.A : Set G)
  let Ag := A.map L.subtype
  let : IsElementaryAbelian 3 Ag := IsElementaryAbelian.map L.subtype
  have hAN : Ag ≤ N := by
    rintro x ⟨a,ha,rfl⟩
    exact normalizes_of_plane_action d (inclusion s.chosen.normalizes a)
      (hES (himage a ha))
  let AN := Ag.subgroupOf N
  let : IsElementaryAbelian 3 AN := IsElementaryAbelian.of_injective
    (subgroupOfEquivOfLe hAN).toMonoidHom (subgroupOfEquivOfLe hAN).injective
  have hcAN : Nat.card AN = 3^2 := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hAN).toEquiv,
      card_map_of_injective L.subtype_injective,hcA]
    decide
  have hJN : J ≤ N := j.input.component.1.trans (Subgroup.centralizer_le_normalizer _)
  let JN := J.subgroupOf N
  let : JN.Normal := normal_subgroupOf_of_le_normalizer (s.local_component_normalizer d J j)
  have hdJ : 3 ∣ Nat.card JN := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hJN).toEquiv]
    exact (ChapterC.C27Source.coreQuotient_three_dvd_from_source j.input).trans
      (card_quotient_dvd_card (pCore 2 J))
  have hrN : primeRank 3 N ≤ 2 :=
    (s.hypothesis.qtke.twoLocal_sqtk
      ⟨d.A,d.ne_bot,IsPGroup.of_card (n := 2) d.card,rfl⟩).stronglyQuasithin
        3 Nat.prime_three (by decide)
  have hne := AN.inf_ne_bot_of_elementary_plane JN
    (by rw [normalizer_eq_top]; exact le_top) hdJ hcAN hrN
  obtain ⟨x,hx,hx1⟩ := SetLike.not_le_iff_exists.mp
    (show ¬ AN ⊓ JN ≤ ⊥ from fun h => hne (bot_unique h))
  obtain ⟨a,ha,he⟩ := hx.1
  have haJ : (a : G) ∈ J := by
    rw [show (a : G) = (x : G) from he]
    exact hx.2
  have ha1 : a ≠ 1 := by
    intro h
    apply hx1
    apply Subtype.ext
    exact he.symm.trans (congrArg Subtype.val h)
  have hfa1 : f a ≠ 1 := by
    intro h
    have hh : (⟨a,ha⟩ : A) = 1 := injective_comp_subtype_of_coprime_ker f hcop A
      (IsElementaryAbelian.isPGroup 3 A) (by simpa using h)
    exact ha1 (congrArg Subtype.val hh)
  have hfa : f a ∈ zpowers cubic := by
    rw [←hEP]
    refine ⟨himage a ha,mem_top _,?_⟩
    intro v hv
    let w := d.coordinates.symm v
    have hw : w.toMul.val ∈ d.A := (mem_pointCoordinateSubspace d.coordinates d.A w).mp
      (by rw [d.plane_space,LinearEquiv.apply_symm_apply]; exact hv)
    have hc := j.input.component.1 haJ
    have hfix : automizerRepresentation V
        (V.normalizerMonoidHom.rangeRestrict (inclusion s.chosen.normalizes a)) w = w := by
      apply Additive.toMul.injective
      apply Subtype.ext
      change (a : G) * w.toMul.val * (a : G)⁻¹ = w.toMul.val
      rw [←hc _ hw,mul_inv_cancel_right]
    have hh := d.equivariant (V.normalizerMonoidHom.rangeRestrict
      (inclusion s.chosen.normalizes a)) w
    rw [hfix] at hh
    change d.coordinates w = rho (f a) (d.coordinates w) at hh
    simpa only [w,LinearEquiv.apply_symm_apply] using hh.symm
  have hpow : (⟨cubic,mem_zpowers cubic⟩ : zpowers cubic) ∈
      zpowers (⟨f a,hfa⟩ : zpowers cubic) :=
    mem_zpowers_of_prime_card ((Nat.card_zpowers cubic).trans orderOf_cubic)
      (fun he => hfa1 (congrArg Subtype.val he))
  obtain ⟨z,hz⟩ := hpow
  refine ⟨⟨(a : G)^z,s.chosen.normalizes (L.zpow_mem a.property z)⟩,
    J.zpow_mem haJ z,L.zpow_mem a.property z,?_,?_⟩
  · have hp : ((a : G)^z)^3 = 1 := by
      have hh : a^3 = 1 := elemPow_eq_one_of_isElementaryAbelian a ha
      have hhG : (a : G)^3 = 1 := congrArg Subtype.val hh
      rw [←zpow_natCast,←zpow_mul, mul_comm, zpow_mul, zpow_natCast,hhG,one_zpow]
    apply orderOf_eq_prime_iff.mpr
    refine ⟨hp,?_⟩
    intro he
    have heL : a^z = 1 := Subtype.ext he
    have hfc : f (a^z) = cubic := by rw [map_zpow]; exact congrArg Subtype.val hz
    rw [heL,map_one] at hfc
    exact cubic_ne_one hfc.symm
  · change f (a^z) = cubic
    rw [map_zpow]
    exact congrArg Subtype.val hz

/-- Every original plane component contains a lift of the specified cubic. -/
theorem Context.component_marked_cubic (s : Context T L V) (d : MarkedPlane V)
    (J : Subgroup G) (j : LocalData T L d J) :
    ∃ n : normalizer (V : Set G), n.val ∈ J ∧
      d.chart (V.normalizerMonoidHom.rangeRestrict n) = cubic := by
  obtain ⟨n,hnJ,_,_,hn⟩ := s.component_marked_cubic_order_three d J j
  exact ⟨n,hnJ,hn⟩

end CFSG.Quasithin.Chapter13.Section03.SourceCompletion.At.OriginalPlaneCentralizers
