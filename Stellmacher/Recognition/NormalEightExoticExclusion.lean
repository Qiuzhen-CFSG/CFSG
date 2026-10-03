module

public import Stellmacher.Recognition.NormalFourOddCoreSetup
public import Theory.SpecificGroups.ExoticTwoGroup.LocalStructure
public import Theory.SpecificGroups.ExoticTwoGroup.CoreFusionCover
public import Theory.SpecificGroups.ExoticTwoGroup.LocalComputations
public import Theory.SpecificGroups.ExoticTwoGroup.CoreGeometry
public import Theory.GroupTheory.CharacteristicCentralizerSylow
public import Theory.GroupTheory.CoprimeQuotientCentralizerFusion
public import Theory.GroupTheory.InvolutionTransfer

/-!
# Exclusion of the exotic Sylow two-group

The normal quotient image preserves membership in the centralizer of the
normal four under fusion inside the central-omega normalizer. Characteristic
centralizer lines and the prime-group normalizer condition then make the
centralizer of `t` fully centralized. In particular `t` cannot fuse to the
central involution. Thompson transfer into the index-two centralizer of the
four fuses `t` to `z₀` once all involutions in the special core fuse to the
central involution. The centralizer of `z₀` would then also be fully
centralized, contradicting their respective orders 16 and 32.

This is a shortened assembly of Janko--Thompson, Math. Z. 113 (1970), p.396.
The intrinsic presentation computations come from `LocalComputations` and
`CoreGeometry`. The supplied fusion in the four and its disjoint commuting
conjugate then give the required core fusion. The final `false_of_presentation`
retains the hypotheses of the ambient recognition application and discharges
both intrinsic computations. No recognition assertion, rank bound on arbitrary
elementary subgroups, or ambient normality of the four is used here.
-/

namespace Stellmacher.Recognition.NormalEightExoticExclusion

open Subgroup NormalFourCentralOmegaTwo
open scoped IsMulCommutative

private theorem no_normal_index_two
    {G : Type*} [Group G] [IsSimpleGroup G] (hns : ¬ Group.IsSolvable G) :
    ∀ K : Subgroup G, K.Normal → K.index ≠ 2 := by
  intro K hK hi
  rcases hK.eq_bot_or_eq_top with hb | ht
  · have hc : Nat.card G = 2 := by simpa only [hb, index_bot] using hi
    let : IsCyclic G := isCyclic_of_prime_card hc
    exact hns (Group.isSolvable_of_comm (fun a b => mul_comm a b))
  · simp only [ht, index_top] at hi
    omega

/-- The actual normal odd-core image preserves centralizer membership under
fusion in the central-omega normalizer. -/
public theorem centralizer_mem_iff_of_omegaNormalizer_conj
    {G : Type*} [Group G] [Finite G] (S : Sylow 2 G) (W : Subgroup S)
    [(fourImage S W).Normal] (g : omegaNormalizer S) (x y : S)
    (hxy : (MulAut.conj (g : G)) (x : G) = (y : G)) :
    x ∈ centralizer (W : Set S) ↔ y ∈ centralizer (W : Set S) := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let N := omegaNormalizer S
  let A := (W.map (S : Subgroup G).subtype).subgroupOf N
  let P := (S : Subgroup G).subgroupOf N
  let q := QuotientGroup.mk' (pPrimeCore 2 N)
  let i := inclusion (sylow_le_omegaNormalizer S)
  have hp : IsPGroup 2 P := S.isPGroup'.comap_subtype
  have hAP : A ≤ P := fun _ hu => map_subtype_le W hu
  have hc : IsConj (i x) (i y) := isConj_iff.mpr ⟨g, Subtype.ext hxy⟩
  have hm := centralizer_mem_iff_of_normal_map_of_isConj q
    (by simpa only [q, QuotientGroup.ker_mk'] using
      pPrimeCore_coprime_card (p := 2) (G := N)) P A hp hAP
    (i x) (i y) x.property y.property hc
  have hmem (u : S) : i u ∈ centralizer (A : Set N) ↔
      u ∈ centralizer (W : Set S) := by
    constructor
    · intro hu v hv
      apply Subtype.ext
      exact congrArg (fun a : N => (a : G))
        (hu (i v) (mem_map_of_mem (S : Subgroup G).subtype hv))
    · intro hu v hv
      obtain ⟨w, hw, he⟩ := hv
      change (w : G) = (v : G) at he
      apply Subtype.ext
      have hh := congrArg (fun a : S => (a : G)) (hu w hw)
      change (w : G) * (u : G) = (u : G) * (w : G) at hh
      change (v : G) * (u : G) = (u : G) * (v : G)
      rwa [he] at hh
  exact (hmem x).symm.trans (hm.trans (hmem y))

private theorem order_eq_of_ambient_isConj
    {G : Type*} [Group G] (S : Subgroup G) (x y : S)
    (h : IsConj (x : G) (y : G)) : orderOf x = orderOf y := by
  obtain ⟨g, hg⟩ := h
  simpa only [Subgroup.orderOf_coe] using SemiconjBy.orderOf_eq (g : G) hg

private theorem centralOmega_eq_line
    {G : Type*} [Group G] [Finite G] (S : Sylow 2 G)
    (hZ : Nat.card (omega₁ (center S) (p := 2)) = 2)
    (z : S) (hz : orderOf z = 2) (hzc : z ∈ center S) :
    centralOmega S = zpowers (z : G) := by
  have hz2 : z ^ 2 = 1 := by simpa only [hz] using pow_orderOf_eq_one z
  have hzZ : (z : G) ∈ centralOmega S := by
    apply mem_map_of_mem
    refine ⟨⟨z, hzc⟩, subset_closure ?_, rfl⟩
    exact (show (⟨z, hzc⟩ : center S) ^ (2 ^ 1) = 1 from
      Subtype.ext (by simpa using hz2))
  apply (eq_of_le_of_card_ge (zpowers_le.mpr hzZ) ?_).symm
  rw [Nat.card_zpowers, Subgroup.orderOf_coe, hz, card_centralOmega, hZ]

/-- Intrinsic core coverage and the supplied conjugate four give ambient
fusion of every core involution to the displayed central involution. -/
public theorem core_fusion_of_cover
    {G : Type*} [Group G] [Finite G] (S : Sylow 2 G)
    (W : Subgroup S) [IsElementaryAbelian 2 W] (hW : Nat.card W = 4)
    (d : ExoticTwoGroup.Presentation S) (hWd : W = d.four)
    (hz : orderOf d.centralInvolution = 2) (hcover : d.CoreFusionCover)
    (hfused : ∀ u v : S, u ∈ W → v ∈ W → orderOf u = 2 → orderOf v = 2 →
      IsConj (u : G) (v : G))
    (g : G)
    (hVS : (W.map (S : Subgroup G).subtype).map (MulAut.conj g).toMonoidHom ≤
      (S : Subgroup G))
    (hdisjoint : Disjoint (W.map (S : Subgroup G).subtype)
      ((W.map (S : Subgroup G).subtype).map (MulAut.conj g).toMonoidHom))
    (hcommute : (W.map (S : Subgroup G).subtype).map (MulAut.conj g).toMonoidHom ≤
      centralizer (W.map (S : Subgroup G).subtype : Set G)) :
    ∀ x : S, x ∈ d.core → orderOf x = 2 →
      IsConj (x : G) (d.centralInvolution : G) := by
  let V := (W.map (S : Subgroup G).subtype).map (MulAut.conj g).toMonoidHom
  let VS := V.subgroupOf (S : Subgroup G)
  let : IsElementaryAbelian 2 (W.map (S : Subgroup G).subtype) :=
    IsElementaryAbelian.map_subtype
  let : IsElementaryAbelian 2 V := IsElementaryAbelian.map _
  let : IsElementaryAbelian 2 VS := IsElementaryAbelian.subgroupOf hVS
  have hc : Nat.card VS = 4 := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hVS).toEquiv,
      card_map_of_injective (MulAut.conj g).injective,
      card_map_of_injective (S : Subgroup G).subtype_injective, hW]
  have hd : Disjoint d.four VS := by
    rw [← hWd]
    apply disjoint_iff.mpr
    apply bot_unique
    intro u hu
    apply Subtype.ext
    exact hdisjoint.le_bot ⟨mem_map_of_mem (S : Subgroup G).subtype hu.1, hu.2⟩
  have hcomm : VS ≤ centralizer (d.four : Set S) := by
    rw [← hWd]
    intro u hu w hw
    exact Subtype.ext (hcommute hu (w : G) (mem_map_of_mem (S : Subgroup G).subtype hw))
  have hzW : d.centralInvolution ∈ W := hWd ▸ d.centralInvolution_mem_four
  intro x hx ho
  obtain ⟨y, hy, hxy⟩ := hcover.apply VS hc hd hcomm x hx ho
  have hxyG := (S : Subgroup G).subtype.map_isConj hxy
  have hyorder : orderOf y = 2 :=
    (order_eq_of_ambient_isConj (S : Subgroup G) x y hxyG).symm.trans ho
  apply hxyG.trans
  rcases hy with hyW | hyV
  · exact hfused y d.centralInvolution (hWd ▸ hyW) hzW hyorder hz
  · obtain ⟨w, ⟨u, hu, rfl⟩, he⟩ := hyV
    have hug : IsConj (u : G) (y : G) := isConj_iff.mpr ⟨g, he⟩
    have huorder : orderOf u = 2 :=
      (order_eq_of_ambient_isConj (S : Subgroup G) u y hug).trans hyorder
    exact hug.symm.trans (hfused u d.centralInvolution hu hzW huorder hz)

private theorem exists_centralizer_sylow_of_local_bound
    {G : Type*} [Group G] [Finite G] (S : Sylow 2 G)
    (N : Subgroup G) (hSN : (S : Subgroup G) ≤ N) (x z : S)
    (hz : orderOf z = 2) (hCN : centralizer ({(z : G)} : Set G) ≤ N)
    (K : Subgroup (centralizer ({x} : Set S))) [K.Characteristic]
    (hK : K.map (centralizer ({x} : Set S)).subtype = zpowers z)
    (hbound : ∀ g : N, ∀ y : S, (MulAut.conj (g : G)) (x : G) = (y : G) →
      Nat.card (centralizer ({y} : Set S)) ≤ Nat.card (centralizer ({x} : Set S))) :
    ∃ T : Sylow 2 (centralizer ({(x : G)} : Set G)),
      (T : Subgroup (centralizer ({(x : G)} : Set G))).map
        (centralizer ({(x : G)} : Set G)).subtype =
          (centralizer ({x} : Set S)).map (S : Subgroup G).subtype := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let C := (centralizer ({x} : Set S)).map (S : Subgroup G).subtype
  let H := centralizer ({(x : G)} : Set G)
  have hnorm : normalizer (C : Set G) ≤ N := by
    have hh := normalizer_le_normalizer_characteristic_map
      (S : Subgroup G).subtype (S : Subgroup G).subtype_injective
      (centralizer ({x} : Set S)) K
    rw [hK, MonoidHom.map_zpowers] at hh
    change normalizer (C : Set G) ≤ normalizer (zpowers (z : G) : Set G) at hh
    rw [normalizer_zpowers_eq_centralizer_of_order_two
      (z : G) ((Subgroup.orderOf_coe z).trans hz)] at hh
    exact hh.trans hCN
  have hCH : C ≤ H := by
    rintro _ ⟨c, hc, rfl⟩
    exact mem_centralizer_singleton_iff.mpr
      (congrArg Subtype.val (mem_centralizer_singleton_iff.mp hc))
  have hp : IsPGroup 2 C := (S.isPGroup'.to_subgroup _).map _
  have hpH : IsPGroup 2 (C.subgroupOf H) := hp.comap_subtype
  obtain ⟨T, hCT⟩ := hpH.exists_le_sylow
  have hCU : C ≤ (T : Subgroup H).map H.subtype := by
    rw [← map_subgroupOf_eq_of_le hCH]
    exact map_mono hCT
  exact ⟨T, prime_overgroup_eq_of_normalizer_control C H N hnorm
    (S.centralizer_prime_overgroup_eq_of_local_card_bound N hSN x hbound)
    _ (T.isPGroup'.map H.subtype) hCU (map_subtype_le _)⟩

/-- Once the finite presentation computations and fusion of the special
core involutions are supplied, transfer and Sylow enlargement exclude the
exotic Sylow group. The remaining input constructors belong to separate modules. -/
public theorem false_of_localStructure_of_core_fusion
    {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]
    (hns : ¬ Group.IsSolvable G) (S : Sylow 2 G)
    (hZ : Nat.card (omega₁ (center S) (p := 2)) = 2)
    (W : Subgroup S) [(fourImage S W).Normal]
    (d : ExoticTwoGroup.Presentation S) (hWd : W = d.four)
    (hl : d.LocalStructure)
    (hcore : ∀ x : S, x ∈ d.core → orderOf x = 2 →
      IsConj (x : G) (d.centralInvolution : G)) : False := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let N := omegaNormalizer S
  have hNZ : N = centralizer ({(d.centralInvolution : G)} : Set G) := by
    change normalizer (centralOmega S : Set G) = _
    rw [centralOmega_eq_line S hZ d.centralInvolution hl.central_order hl.central_mem,
      normalizer_zpowers_eq_centralizer_of_order_two _
        ((Subgroup.orderOf_coe d.centralInvolution).trans hl.central_order)]
  have heven (g : N) (x y : S)
      (hxy : (MulAut.conj (g : G)) (x : G) = (y : G)) :
      x ∈ d.evenSubgroup ↔ y ∈ d.evenSubgroup := by
    rw [hl.even_eq_centralizer, ← hWd]
    exact centralizer_mem_iff_of_omegaNormalizer_conj S W g x y hxy
  have htbound (g : N) (y : S)
      (hxy : (MulAut.conj (g : G)) (d.t : G) = (y : G)) :
      Nat.card (centralizer ({y} : Set S)) ≤ Nat.card (centralizer ({d.t} : Set S)) := by
    have hy : orderOf y = 2 := (order_eq_of_ambient_isConj (S : Subgroup G) d.t y
      (isConj_iff.mpr ⟨(g : G), hxy⟩)).symm.trans hl.t_order
    have hyout : y ∉ d.evenSubgroup := fun hh =>
      hl.t_not_even ((heven g d.t y hxy).mpr hh)
    rcases hl.odd_classes y hy hyout with hc | hc
    · exact (card_centralizer_eq_of_isConj y d.t hc).le
    · exact (card_centralizer_eq_of_isConj y (d.t * d.z₀) hc).le.trans
        (hl.tz₀_centralizer_card.trans hl.t_centralizer_card.symm).le
  obtain ⟨Kt, hKt, hKtline⟩ := hl.characteristic_line d.t (by simp)
  let : Kt.Characteristic := hKt
  obtain ⟨T, hT⟩ := exists_centralizer_sylow_of_local_bound S N
    (sylow_le_omegaNormalizer S) d.t d.centralInvolution hl.central_order
    hNZ.ge Kt hKtline htbound
  have hTcard : Nat.card T = 32 := by
    have hh := congrArg (fun H : Subgroup G => Nat.card H) hT
    rw [card_map_of_injective (centralizer ({(d.t : G)} : Set G)).subtype_injective,
      card_map_of_injective (S : Subgroup G).subtype_injective,
      hl.t_centralizer_card] at hh
    exact hh
  have hnot : ¬ IsConj (d.t : G) (d.centralInvolution : G) := by
    intro hc
    have hSZ : (S : Subgroup G) ≤ centralizer ({(d.centralInvolution : G)} : Set G) := by
      intro s hs
      exact mem_centralizer_singleton_iff.mpr
        (congrArg Subtype.val (mem_center_iff.mp hl.central_mem ⟨s, hs⟩))
    let Z := S.subtype hSZ
    have hZcard : Nat.card Z = Nat.card S :=
      Nat.card_congr (subgroupOfEquivOfLe hSZ).toEquiv
    have hh : Nat.card T = Nat.card Z := by
      rw [T.card_eq_multiplicity, Z.card_eq_multiplicity,
        card_centralizer_eq_of_isConj _ _ hc]
    rw [hTcard, hZcard, d.card] at hh
    omega
  obtain ⟨u, htu, hu⟩ := S.exists_isConj_mem_of_index_two (no_normal_index_two hns)
    d.evenSubgroup hl.even_index d.t hl.t_order
  have huorder : orderOf u = 2 :=
    (order_eq_of_ambient_isConj (S : Subgroup G) d.t u htu).symm.trans hl.t_order
  have htz₀ : IsConj (d.t : G) (d.z₀ : G) := by
    rcases hl.even_classes u huorder hu with huc | huz
    · exact (hnot (htu.trans (hcore u huc huorder))).elim
    · exact htu.trans ((S : Subgroup G).subtype.map_isConj huz)
  have hzbound (g : N) (y : S)
      (hxy : (MulAut.conj (g : G)) (d.z₀ : G) = (y : G)) :
      Nat.card (centralizer ({y} : Set S)) ≤ Nat.card (centralizer ({d.z₀} : Set S)) := by
    have hc : IsConj (d.z₀ : G) (y : G) := isConj_iff.mpr ⟨(g : G), hxy⟩
    have hy : orderOf y = 2 := (order_eq_of_ambient_isConj
      (S : Subgroup G) d.z₀ y hc).symm.trans hl.z₀_order
    have hyin := (heven g d.z₀ y hxy).mp hl.z₀_mem_even
    rcases hl.even_classes y hy hyin with hycore | hyz
    · exact (hnot (htz₀.trans (hc.trans (hcore y hycore hy)))).elim
    · exact (card_centralizer_eq_of_isConj y d.z₀ hyz).le
  obtain ⟨Kz, hKz, hKzline⟩ := hl.characteristic_line d.z₀ (by simp)
  let : Kz.Characteristic := hKz
  obtain ⟨Z, hZZ⟩ := exists_centralizer_sylow_of_local_bound S N
    (sylow_le_omegaNormalizer S) d.z₀ d.centralInvolution hl.central_order
    hNZ.ge Kz hKzline hzbound
  have hZcard : Nat.card Z = 16 := by
    have hh := congrArg (fun H : Subgroup G => Nat.card H) hZZ
    rw [card_map_of_injective (centralizer ({(d.z₀ : G)} : Set G)).subtype_injective,
      card_map_of_injective (S : Subgroup G).subtype_injective,
      hl.z₀_centralizer_card] at hh
    exact hh
  have hh : Nat.card T = Nat.card Z := by
    rw [T.card_eq_multiplicity, Z.card_eq_multiplicity,
      card_centralizer_eq_of_isConj _ _ htz₀]
  omega

/-- The supplied fused, disjoint commuting four completes the ambient
exclusion once the two intrinsic presentation computations are constructed. -/
public theorem false_of_localStructure_of_cover
    {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]
    (hns : ¬ Group.IsSolvable G) (S : Sylow 2 G)
    (hZ : Nat.card (omega₁ (center S) (p := 2)) = 2)
    (W : Subgroup S) [IsElementaryAbelian 2 W] (hW : Nat.card W = 4)
    [(fourImage S W).Normal]
    (d : ExoticTwoGroup.Presentation S) (hWd : W = d.four)
    (hl : d.LocalStructure) (hcover : d.CoreFusionCover)
    (hfused : ∀ u v : S, u ∈ W → v ∈ W → orderOf u = 2 → orderOf v = 2 →
      IsConj (u : G) (v : G))
    (g : G)
    (hVS : (W.map (S : Subgroup G).subtype).map (MulAut.conj g).toMonoidHom ≤
      (S : Subgroup G))
    (hdisjoint : Disjoint (W.map (S : Subgroup G).subtype)
      ((W.map (S : Subgroup G).subtype).map (MulAut.conj g).toMonoidHom))
    (hcommute : (W.map (S : Subgroup G).subtype).map (MulAut.conj g).toMonoidHom ≤
      centralizer (W.map (S : Subgroup G).subtype : Set G)) : False :=
  false_of_localStructure_of_core_fusion hns S hZ W d hWd hl
    (core_fusion_of_cover S W hW d hWd hl.central_order hcover hfused
      g hVS hdisjoint hcommute)

/-- The exotic presentation cannot occur with a normal actual quotient image
and a fused four admitting a disjoint commuting conjugate in the Sylow group.
The presentation itself supplies all local computations and core coverage. -/
public theorem false_of_presentation_of_fused_four
    {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]
    (hns : ¬ Group.IsSolvable G) (S : Sylow 2 G)
    (hZ : Nat.card (omega₁ (center S) (p := 2)) = 2)
    (W : Subgroup S) [IsElementaryAbelian 2 W] (hW : Nat.card W = 4)
    [(fourImage S W).Normal]
    (d : ExoticTwoGroup.Presentation S)
    (hWd : W = closure ({d.a ^ 2, d.b ^ 2} : Set S))
    (hfused : ∀ u v : S, u ∈ W → v ∈ W → orderOf u = 2 → orderOf v = 2 →
      IsConj (u : G) (v : G))
    (g : G)
    (hVS : (W.map (S : Subgroup G).subtype).map (MulAut.conj g).toMonoidHom ≤
      (S : Subgroup G))
    (hdisjoint : Disjoint (W.map (S : Subgroup G).subtype)
      ((W.map (S : Subgroup G).subtype).map (MulAut.conj g).toMonoidHom))
    (hcommute : (W.map (S : Subgroup G).subtype).map (MulAut.conj g).toMonoidHom ≤
      centralizer (W.map (S : Subgroup G).subtype : Set G)) : False :=
  false_of_localStructure_of_cover hns S hZ W hW d hWd
    d.localStructure d.coreFusionCover hfused g hVS hdisjoint hcommute

set_option linter.unusedVariables false in
/-- Exclude the supplied exotic order-256 Sylow in the normal-eight application.
The full ambient hypotheses are retained for the consumer; after the marked
presentation and moving four are supplied, the preceding stronger theorem
needs no additional rank bound, recognition theorem, or fusion assertion. -/
public theorem false_of_presentation
    {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]
    (hns : ¬ Group.IsSolvable G) (hN : Stellmacher.IsNTwoGroup G)
    (S : Sylow 2 G)
    (A : Subgroup S) [IsElementaryAbelian 2 A] (hA : 8 ≤ Nat.card A)
    (hnonab : ¬ IsMulCommutative S)
    (hZ : Nat.card (omega₁ (center S) (p := 2)) = 2)
    (hno : ¬ ∃ E : Subgroup S, E.Normal ∧ IsElementaryAbelian 2 E ∧ 8 ≤ Nat.card E)
    (W : Subgroup S) [W.Normal] [IsElementaryAbelian 2 W] (hW : Nat.card W = 4)
    (hunique : ∀ F : Subgroup S, F.Normal → IsElementaryAbelian 2 F →
      Nat.card F = 4 → F = W)
    [(fourImage S W).Normal]
    (d : ExoticTwoGroup.Presentation S)
    (hWd : W = closure ({d.a ^ 2, d.b ^ 2} : Set S))
    (hfused : ∀ u v : S, u ∈ W → v ∈ W → orderOf u = 2 → orderOf v = 2 →
      IsConj (u : G) (v : G))
    (g : G)
    (hVS : (W.map (S : Subgroup G).subtype).map (MulAut.conj g).toMonoidHom ≤
      (S : Subgroup G))
    (hdisjoint : Disjoint (W.map (S : Subgroup G).subtype)
      ((W.map (S : Subgroup G).subtype).map (MulAut.conj g).toMonoidHom))
    (hcommute : (W.map (S : Subgroup G).subtype).map (MulAut.conj g).toMonoidHom ≤
      centralizer (W.map (S : Subgroup G).subtype : Set G)) : False :=
  false_of_presentation_of_fused_four hns S hZ W hW d hWd hfused
    g hVS hdisjoint hcommute

end Stellmacher.Recognition.NormalEightExoticExclusion
