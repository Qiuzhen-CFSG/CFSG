module
public import CFSG.Quasithin.Chapter2.Section05.SmallComponentExclusion.OuterComplement
public import Theory.GroupTheory.DisjointCommutingProduct
/-!
# The original PSL₃(3) shadow is a central involution times Aut(PSL₃(3))

Residual invariance fixes the projection mark, so it equals z. The crossing
adjustment and cyclic-four fixer lift then give y²=z. The kernel is ⟨t⟩,
and the action on A=K⟨y⟩ is faithful and onto the full automorphism group.
Consequently H is the internal direct product ⟨t⟩×A. The final consumer
selects every central mark from the original source tuple.
Source: Aschbacher--Smith 2.5.15, printed pp.558--559.
-/
public section
namespace CFSG.Quasithin.Chapter2.Section05
open Subgroup Theory.GroupTheory A6Shadow.Frattini ComponentRefinement ComponentSelection ClassificationModels
variable {G : Type*} [Group G] [Finite G] {H K M U L : Subgroup G}
  {S : Sylow 2 H} {z : G}

theorem linear_three_source_marked_split
    (c : MathieuSourceSetup H K M S z) [(K.subgroupOf H).Normal]
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : gammaEvenZero (Chapter1.He G) M = ∅)
    (hgen : H = K ⊔ (S : Subgroup H).map H.subtype) (hb : ¬ IsBenderModel K)
    (hp : (U,L) ∈ largestLocalPairs M H) (hUS : U ≤ (S : Subgroup H).map H.subtype)
    (e : K ≃* Matrix.PSL3Three.PSL)
    (t : G) (ht : orderOf t=2) (htC : t∈twoCore H)
    (htZ : t∈centerIn ((S : Subgroup H).map H.subtype))
    (hZ : IsKleinFour (centerIn ((S : Subgroup H).map H.subtype)))
    (k : K) (hk : orderOf k=2) (hkZ : (k:G)∈centerIn ((S : Subgroup H).map H.subtype))
    (hspan : centerIn ((S : Subgroup H).map H.subtype)=zpowers t ⊔ zpowers (k:G)) :
    (k:G)=z ∧ ∃ y : H, y∈S ∧ orderOf y=4 ∧ (y:G)^2=z ∧
      MathieuSourceSetup.componentAction c y ∉ MulAut.innerSubgroup K ∧
      let A := K ⊔ zpowers (y:G)
      ∃ hAH : A≤H, Function.Bijective
        ((MathieuSourceSetup.componentAction c).comp (inclusion hAH)) ∧
        H=zpowers t ⊔ A ∧ Disjoint (zpowers t) A ∧ zpowers t≤centralizer (A:Set G) := by
  let Y := (S:Subgroup H).map H.subtype
  have hres := (MathieuSourceSetup.small_component_centralizer_residual c hG hempty hgen
    (Or.inl ⟨e⟩) t ht htC htZ).2.2
  have hN := local_residual_normalized_by_sylow_normalizer K Y (Or.inl ⟨e⟩) k hk t hspan hres
  have hout : ¬Y≤K⊔centralizer (K:Set G) := by
    intro hin
    exact small_component_inner_residual_false c hG hempty hgen hb hp hUS (Or.inl ⟨e⟩)
      hin t ht htC htZ hZ k hk hkZ hspan hres
  obtain ⟨x,hxT,hxS,hxN,_⟩ := exists_outside_normalizer_square_mem Y c.T c.T.isPGroup' c.sylow_lt
  have hxR := hN hxN
  have hkG : orderOf (k:G)=2 := (Subgroup.orderOf_coe k).trans hk
  have hcent := local_residual_ambient_center K (Or.inl ⟨e⟩) k hk
  have hxk : x∈normalizer (zpowers (k:G):Set G) := by
    rw [←hcent]
    exact normalizes_centerIn (le_rfl : normalizer ((GLTwoThreeLocal.residual k).map K.subtype:Set G)≤
      normalizer ((GLTwoThreeLocal.residual k).map K.subtype:Set G)) hxR
  rw [normalizer_zpowers_eq_centralizer_of_order_two _ hkG] at hxk
  have hkfix : x⁻¹*(k:G)*x=(k:G) := by
    have hh := mem_centralizer_singleton_iff.mp hxk
    calc x⁻¹*(k:G)*x = x⁻¹*((k:G)*x) := mul_assoc _ _ _
         _ = x⁻¹*(x*(k:G)) := by rw [hh]
         _ = (k:G) := inv_mul_cancel_left _ _
  have hkz := MathieuSourceSetup.source_fixed_projection c hgen t ht htC htZ hZ
    x hxT hxN hxS k hkG hkZ hkfix
  obtain ⟨x,hxT,hxS,hxN,hxR⟩ := local_residual_crossing_adjustment c (Or.inl ⟨e⟩)
    k hk hkZ hxT hxS hxN hxR
  have hcore := linear_three_source_core_eq_central_involution c hG hempty hgen hb hp hUS e
    t ht htC htZ hZ k hk hkZ hspan
  have hker : (MathieuSourceSetup.componentAction c).ker=(zpowers t).subgroupOf H := by
    rw [normal_component_source_action_ker c hG hempty hgen,hcore]
  obtain ⟨y,hyS,hyR,hyo,hy4,hy2,hC⟩ := linear_three_outer_residual_lift c hG hempty hgen e k hk
    hout (Y.le_normalizer.trans hN)
  have hCY : Y ⊓ centralizer ((GLTwoThreeLocal.residual k).map K.subtype:Set G)=
      H ⊓ centralizer ((GLTwoThreeLocal.residual k).map K.subtype:Set G) := le_antisymm
    (inf_le_inf_right _ (map_subtype_le _)) (le_inf
      (linear_three_residual_centralizer_le_source_sylow c hG hempty hgen e k hk (Y.le_normalizer.trans hN))
      inf_le_right)
  have hC' : Y ⊓ centralizer ((GLTwoThreeLocal.residual k).map K.subtype:Set G)=
      zpowers t ⊔ zpowers (y:G) := by rw [hCY,hC,hcore]
  have hsq := linear_three_outer_lift_square c hgen t ht htC htZ hZ k hkz y hyS hy2 hker hC'
    hxT hxS hxN hxR
  have hoy : orderOf y=4 := by
    have hy2ne : y^2≠1 := by
      intro he
      have hz1 : z=1 := hsq.symm.trans (congrArg Subtype.val he)
      have hz := c.involution
      rw [hz1,orderOf_one] at hz
      omega
    have hy4one : y^4=1 := by
      apply Subtype.ext
      change (y:G)^4=1
      rw [show 4=2*2 from rfl,pow_mul,hsq,←c.involution]
      exact pow_orderOf_eq_one z
    exact orderOf_eq_prime_pow (p:=2) (n:=1) (by simpa only [pow_one] using hy2ne) hy4one
  obtain ⟨hAH,hbij⟩ := linear_three_outer_complement_equiv c e y hyo hoy (by rw [hsq,←hkz]; exact k.property)
  let A := K⊔zpowers (y:G)
  have hspanH : H=zpowers t⊔A := by
    rw [linear_three_source_outer_generation c hG hempty hgen e y hyo,hcore]
    dsimp only [A]
    ac_rfl
  have hd : Disjoint (zpowers t) A := by
    apply disjoint_def.mpr
    intro a haT haA
    have hah : a∈H := hAH haA
    have hh : (MathieuSourceSetup.componentAction c) ⟨a,hah⟩=1 := by
      change (⟨a,hah⟩:H)∈(MathieuSourceSetup.componentAction c).ker
      rw [hker];exact haT
    have hf : ((MathieuSourceSetup.componentAction c).comp (inclusion hAH)) ⟨a,haA⟩ =
        ((MathieuSourceSetup.componentAction c).comp (inclusion hAH)) 1 := by
      rw [map_one]
      exact hh
    exact congrArg Subtype.val (hbij.1 hf)
  have htH := (MathieuSourceSetup.central_core_involution_centralizer c hgen t ht htC htZ).1
  have htc : zpowers t≤centralizer (A:Set G) := zpowers_le.mpr (fun a ha =>
    (mem_centralizer_singleton_iff.mp (htH (hAH ha))))
  exact ⟨hkz,y,hyS,hoy,hsq,hyo,hAH,hbij,hspanH,hd,htc⟩
end CFSG.Quasithin.Chapter2.Section05

namespace CFSG.Quasithin.Chapter2.Section05
open Subgroup Theory.GroupTheory A6Shadow.Frattini ComponentRefinement ComponentSelection ClassificationModels
variable {G : Type*} [Group G] [Finite G] {H K M U L : Subgroup G}
  {S : Sylow 2 H} {z : G}

theorem linear_three_source_direct_product
    (c : MathieuSourceSetup H K M S z) [(K.subgroupOf H).Normal]
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : gammaEvenZero (Chapter1.He G) M = ∅)
    (hgen : H = K ⊔ (S : Subgroup H).map H.subtype) (hb : ¬ IsBenderModel K)
    (hp : (U,L) ∈ largestLocalPairs M H) (hUS : U ≤ (S : Subgroup H).map H.subtype)
    (e : K ≃* Matrix.PSL3Three.PSL) :
    ∃ t : G, orderOf t=2 ∧ t∈twoCore H ∧ t∈centerIn ((S:Subgroup H).map H.subtype) ∧
      twoCore H=zpowers t ∧ ∃ y : H, y∈S ∧ orderOf y=4 ∧ (y:G)^2=z ∧
      let A := K⊔zpowers (y:G)
      Nonempty (A ≃* MulAut Matrix.PSL3Three.PSL) ∧ H=zpowers t⊔A ∧
        Disjoint (zpowers t) A ∧ zpowers t≤centralizer (A:Set G) ∧
        Nonempty (zpowers t × A ≃* H) := by
  let Y := (S : Subgroup H).map H.subtype
  obtain ⟨t,k,ht,hk,htC,hcore,hline,_,hspanK,hZ,_⟩ :=
    ComponentSelection.MathieuSourceSetup.source_central_marks c hG hempty hgen hb
  have htZ : t ∈ centerIn Y := by
    have hh : t ∈ centerIn Y ⊓ twoCore H := hcore ▸ mem_zpowers t
    exact hh.1
  have hKY : Y ≤ normalizer (K : Set G) := (map_subtype_le _).trans
    ((normal_subgroupOf_iff_le_normalizer c.component_le).mp inferInstance)
  have horbit : componentOrbit K Y = K := le_antisymm
    (iSup_conjugates_le_of_le_normalizer _ _ _ le_rfl hKY) (le_componentOrbit _ _)
  have hkZK : k ∈ centerIn Y ⊓ K := by
    rw [horbit] at hline
    exact hline ▸ mem_zpowers k
  let zK : K := ⟨k,hkZK.2⟩
  have hzK : orderOf zK = 2 := by simpa only [zK,Subgroup.orderOf_mk] using hk
  have hN := linear_three_source_core_eq_central_involution c hG hempty hgen hb hp hUS e
    t ht htC htZ hZ zK hzK hkZK.1 hspanK
  obtain ⟨_,y,hyS,hy4,hy2,_,hAH,hbij,hspanH,hd,hcomm⟩ := linear_three_source_marked_split
    c hG hempty hgen hb hp hUS e t ht htC htZ hZ zK hzK hkZK.1 hspanK
  let A := K⊔zpowers (y:G)
  let f : A ≃* MulAut Matrix.PSL3Three.PSL :=
    (MulEquiv.ofBijective ((MathieuSourceSetup.componentAction c).comp (inclusion hAH)) hbij).trans
      (MulAut.congr e)
  obtain ⟨p,_⟩ := exists_mulEquiv_prod_sup_of_disjoint_of_commuting (zpowers t) A hd hcomm
  refine ⟨t,ht,htC,htZ,hN,y,hyS,hy4,hy2,⟨f⟩,hspanH,hd,hcomm,?_⟩
  exact ⟨p.trans (MulEquiv.subgroupCongr hspanH.symm)⟩
end CFSG.Quasithin.Chapter2.Section05
