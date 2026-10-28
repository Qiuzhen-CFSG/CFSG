module

public import Theory.GroupTheory.Recognition.UnitaryFourThree.CubicNormalizer.LineNormalizer.Source
public import Theory.GroupTheory.Recognition.UnitaryFourThree.CubicLine.SylowProduct
public import Theory.GroupTheory.Recognition.UnitaryFourThree.CubicLine.SylowCensus
public import Theory.GroupTheory.Recognition.UnitaryFourThree.CubicGeometry.Normalizer
public import Theory.GroupTheory.Recognition.UnitaryFourThree.CubicGeometry.TwoSylow
public import Theory.GroupTheory.Recognition.UnitaryFourThree.CubicGeometry.FixedPlanes

public section
open Subgroup
namespace Theory.GroupTheory.Recognition.UnitaryFourThree.IsType
variable {G:Type*} [Group G] [Finite G] {z:G} (h:IsType z)
include h in
theorem cubic_line_marked_quaternion_sylow (P:Sylow 3 (centralizer z))
    (m:CubicNormalizer.ReflectedMarking z ((P:Subgroup (centralizer z)).map (centralizer z).subtype))
    (actors:QuaternionIndependentCubics h.toCentralizerHypothesis.factorData.leftCore
      h.toCentralizerHypothesis.factorData.rightCore)
    (ha:actors.A=(P:Subgroup (centralizer z)).map (centralizer z).subtype) :
    ∃T:Sylow 2 (normalizer (zpowers (actors.x:G):Set G)),Nonempty (T≃*QuaternionGroup 4) := by
  let d:=h.toCentralizerHypothesis.factorData
  let W:=zpowers (actors.x:G)
  let r:=m.s*m.t
  let S:=d.rightCore⊔zpowers r
  have hB:Nonempty (d.leftCore≃*QuaternionGroup 2):=⟨Factors.factorCoreEquiv d.left d.left_model.some⟩
  have hC:Nonempty (d.rightCore≃*QuaternionGroup 2):=⟨Factors.factorCoreEquiv d.right d.right_model.some⟩
  have hi:Nat.card (d.leftCore⊓d.rightCore:Subgroup G)=2:=by
    rw [d.core_intersection h.involution,Nat.card_zpowers,h.involution]
  have hcomm:∀b∈d.leftCore,∀c∈d.rightCore,b*c=c*b:=fun b hb c hc=>
    d.factors_commute h.involution b (pCoreIn_le 2 d.left hb) c (pCoreIn_le 2 d.right hc)
  have hnormal:centralizer z≤normalizer (d.leftCore⊔d.rightCore:Subgroup G):=by
    rw [d.core_span h.involution]
    exact CentralizerHypothesis.centralizer_normalizes_core
  have hr:r∈centralizer z:=m.rotation_centralizes
  have hinv:∀x∈actors.A,r*x*r⁻¹=x⁻¹:=by rw [ha];exact m.rotation_inverts
  have hrC:r∈normalizer (d.rightCore:Set G):=
    (actors.normalizes_factors_of_inversion hB hC hi hcomm r (hnormal hr) hinv).2
  have hzC:z∈d.rightCore:=(d.core_intersection h.involution ▸ mem_zpowers z).2
  have hc3:(actors.actionC actors.y)^3=1:=by
    have hy3:actors.y^3=1:=Subtype.ext (actors.y_order ▸ pow_orderOf_eq_one (actors.y:G))
    rw [←map_pow,hy3,map_one]
  have hSmodel:Nonempty (S≃*QuaternionGroup 4):=
    quaternion_sixteen_of_cubic_inverter d.rightCore hC.some z r hzC h.involution hrC
      m.rotation_square (actors.actionC actors.y) hc3 actors.y_actionC_ne_one
      (actors.inverts_right_action r hrC (hinv actors.y actors.y.property))
  have hAX:actors.A≤centralizer z:=ha ▸ map_subtype_le _
  have hWH:W≤centralizer z:=zpowers_le.mpr (hAX actors.x.property)
  have hCH:d.rightCore≤centralizer z:=(pCoreIn_le 2 d.right).trans (d.right_le.trans (map_subtype_le _))
  have hSC:S≤centralizer z:=sup_le hCH (zpowers_le.mpr hr)
  have hSN:S≤normalizer (W:Set G):=by
    obtain ⟨_,_,_,_,hKN,_⟩:=actors.complement_of_inverter hC hcomm z r h.involution hzC hrC
      m.rotation_square hinv
    exact (sup_le (le_sup_left.trans le_sup_left) le_sup_right).trans hKN
  have hW:Nat.card W=3:=by rw [Nat.card_zpowers,actors.x_order]
  have hfixed:Nonempty ((core z⊓Subgroup.centralizer (W:Set G):Subgroup G)≃*QuaternionGroup 2):=by
    rw [←d.core_span h.involution,actors.fixed_core_left hB hi hcomm]
    exact hC
  obtain ⟨E,hEE,hE,hEH,hEQ,_⟩:=h.exists_plane_with_core_eight
  let :IsElementaryAbelian 2 E:=hEE
  have hb:Nat.card (normalizer (W:Set G)⊓centralizer z:Subgroup G)∣144:=by
    simpa only [inf_comm] using h.cubic_line_normalizer_card_dvd W hW hWH hfixed E hEH hE hEQ
  obtain ⟨T,_,hT⟩:=exists_sylow_of_quaternion_sixteen_local_bound (normalizer (W:Set G)) S z
    h.involution (mem_sup_left hzC) (le_inf hSN hSC) hSmodel.some hb
  exact ⟨T,hT⟩
end Theory.GroupTheory.Recognition.UnitaryFourThree.IsType

namespace Theory.GroupTheory.Recognition.UnitaryFourThree.CubicGeometry
variable {G:Type*} [Group G] [Finite G] {z:G}
structure SourceData (h:IsType z) (P:Sylow 3 (centralizer z)) where
  marking : CubicNormalizer.ReflectedMarking z ((P:Subgroup (centralizer z)).map (centralizer z).subtype)
  actors : QuaternionIndependentCubics h.toCentralizerHypothesis.factorData.leftCore
    h.toCentralizerHypothesis.factorData.rightCore
  actors_eq : actors.A=(P:Subgroup (centralizer z)).map (centralizer z).subtype

namespace SourceData
variable {h:IsType z} {P:Sylow 3 (centralizer z)}
abbrev X (_d:SourceData h P):Subgroup G:=(P:Subgroup (centralizer z)).map (centralizer z).subtype
abbrev V (d:SourceData h P):Subgroup G:=CubicNormalizer.oddKernel d.X
abbrev W (d:SourceData h P):Subgroup G:=zpowers (d.actors.x:G)
abbrev D (d:SourceData h P):Subgroup G:=CubicLine.oddKernel d.W
noncomputable abbrev J (d:SourceData h P):Subgroup G:=h.toCentralizerHypothesis.factorData.rightCore⊔zpowers (d.actors.y:G)
noncomputable abbrev K (d:SourceData h P):Subgroup G:=d.J⊔zpowers (d.marking.s*d.marking.t)
abbrev Q (d:SourceData h P):Subgroup G:=d.V⊔d.D
end SourceData

structure SourceConfiguration (h:IsType z) (P:Sylow 3 (centralizer z)) extends SourceData h P where
  line_card : Nat.card toSourceData.W=3
  kernel_elementary : IsElementaryAbelian 3 toSourceData.V
  kernel_card : Nat.card toSourceData.V=81
  fixed_quaternion : Nonempty ((core z⊓Subgroup.centralizer (toSourceData.W:Set G):Subgroup G)≃*QuaternionGroup 2)
  quaternion_sylow : ∃T:Sylow 2 (normalizer (toSourceData.W:Set G)),Nonempty (T≃*QuaternionGroup 4)
  odd_split : normalizer (toSourceData.W:Set G)=toSourceData.D⊔(normalizer (toSourceData.W:Set G)⊓centralizer z)
  odd_card : Nat.card toSourceData.D=243
  odd_extraspecial : IsExtraspecial 3 toSourceData.D
  odd_cube : ∀x∈toSourceData.D,x^3=1
  odd_fitting : (Theory.GroupTheory.generalizedFitting (normalizer (toSourceData.W:Set G))).map
    (normalizer (toSourceData.W:Set G)).subtype=toSourceData.D
  odd_centralizer : Subgroup.centralizer (toSourceData.D:Set G)=toSourceData.W
  odd_fixed : toSourceData.D⊓centralizer z=toSourceData.W
  odd_inversion : ∀x∈toSourceData.D,z*x*z⁻¹*x∈toSourceData.W
  odd_derived : ⁅toSourceData.D,toSourceData.D⁆≤toSourceData.W
  intersection : toSourceData.V⊓toSourceData.D=⁅toSourceData.V,zpowers z⁆⊔toSourceData.W
  intersection_card : Nat.card (toSourceData.V⊓toSourceData.D:Subgroup G)=27
  special_model : Nonempty (toSourceData.J≃*Matrix.SpecialLinearGroup (Fin 2) (ZMod 3))
  special_card : Nat.card toSourceData.J=24
  complement_card : Nat.card toSourceData.K=48
  complement_le : toSourceData.K≤centralizer z⊓normalizer (toSourceData.W:Set G)
  complement_product : normalizer (toSourceData.W:Set G)=toSourceData.D⊔toSourceData.K
  complement_disjoint : Disjoint toSourceData.D toSourceData.K
  special_normalized : marking.s*marking.t∈normalizer (toSourceData.J:Set G)
  sylow : Sylow 3 G
  sylow_eq : (sylow:Subgroup G)=toSourceData.Q
  sylow_card : Nat.card toSourceData.Q=729
  sylow_center : (center sylow).map (sylow:Subgroup G).subtype=toSourceData.W
  common_normalizer : normalizer (sylow:Set G)=normalizer (toSourceData.V:Set G)⊓normalizer (toSourceData.W:Set G)
  normalizer_card : Nat.card (normalizer (sylow:Set G))=2916
  normalizer_index : toSourceData.V.relIndex (normalizer (sylow:Set G))=36
  maximum : ∀B:Subgroup G,IsMulCommutative B→B≤toSourceData.Q→
    (¬B≤toSourceData.V→Nat.card B≤27) ∧ (81≤Nat.card B→B=toSourceData.V)
end Theory.GroupTheory.Recognition.UnitaryFourThree.CubicGeometry

namespace Theory.GroupTheory.Recognition.UnitaryFourThree.IsType
variable {G:Type*} [Group G] [Finite G] {z:G} (h:IsType z)
include h in
theorem original_cubic_source_configuration (P:Sylow 3 (centralizer z)) :
    Nonempty (CubicGeometry.SourceConfiguration h P) := by
  obtain ⟨m,hmove⟩:=h.exists_reflected_moved_line_source P
  obtain ⟨actors,ha,hW,hJ,hJc,hK,hKN,hWK,hl,hg,hd,hrJ,hfixed⟩:=h.cubic_line_complement_marked P m
  let d:CubicGeometry.SourceData h P:=⟨m,actors,ha⟩
  have hWX:d.W≤d.X:=zpowers_le.mpr (ha.le actors.x.property)
  have hWH:d.W≤centralizer z:=hWX.trans (map_subtype_le _)
  have hs:normalizer (d.W:Set G)=d.D⊔(normalizer (d.W:Set G)⊓centralizer z):=by
    rw [inf_comm,hl,←sup_assoc,sup_eq_left.mpr (CubicLine.le_oddKernel d.W hW)]
    exact hg
  have hS:=h.cubic_line_marked_quaternion_sylow P m actors ha
  obtain ⟨hV,hVc⟩:=h.original_cubic_kernel_eighty_one P
  obtain ⟨hcap,hcapc⟩:=h.cubic_line_kernel_intersection d.X d.W (h.cubic_sylow_image_card P)
    (map_subtype_le _) hW hWX hfixed hs hV hVc
  have hdisp:⁅d.V,zpowers z⁆≤d.D:=
    (le_sup_left.trans hcap.ge).trans inf_le_right
  obtain ⟨F,hFV,hF,_,hFN,hFi⟩:=hmove d.D hdisp
  obtain ⟨hfit,hD,hCD,he,hpow⟩:=h.original_cubic_line_fitting_of_moved_line P d.W F hW hWX
    hfixed hs hS hF (hFV.trans inf_le_left) (hFV.trans inf_le_right) hFN hFi
  obtain ⟨hQc,hcenter,T,hT⟩:=h.cubic_line_sylow P d.W d.K hW hWX hfixed hs hK
    (hKN.trans inf_le_right) hg hd hD hCD
  have hcT:(center T).map (T:Subgroup G).subtype=d.W:=by
    rw [hT]
    exact hcenter
  have hN:=h.cubic_kernel_common_normalizer P actors ha hs hD he T hT hcT
  have hJK:d.J≤d.K:=le_sup_left
  let : (d.J.subgroupOf d.K).Normal:=normal_subgroupOf_of_le_normalizer
    (sup_le d.J.le_normalizer (zpowers_le.mpr hrJ))
  have hcJ:Nat.card (d.J.subgroupOf d.K)=24:=
    (Nat.card_congr (subgroupOfEquivOfLe hJK).toEquiv).trans hJc
  have hj:(d.J.subgroupOf d.K)≃*Matrix.SpecialLinearGroup (Fin 2) (ZMod 3):=
    (subgroupOfEquivOfLe hJK).trans hJ.some
  have hcount:=cubic_sylow_count_of_sl2_three_index_two (d.J.subgroupOf d.K) hK hcJ hj
  obtain ⟨hnc,hni⟩:=h.cubic_line_normalizer_census_of_complement P d.W d.K hW hWX hfixed hs
    hK (hKN.trans inf_le_right) hg hd hcount hD
  have hNle:normalizer (T:Set G)≤normalizer (d.W:Set G):=hN.le.trans inf_le_right
  have hNc:Nat.card (normalizer (T:Set G))=2916:=by
    change Nat.card (normalizer ((d.V⊔d.D:Subgroup G):Set G)⊓normalizer (d.W:Set G):Subgroup G)=2916 at hnc
    rw [←hT] at hnc
    change Nat.card (normalizer (T:Set G)⊓normalizer (d.W:Set G):Subgroup G)=2916 at hnc
    rw [inf_eq_left.mpr hNle] at hnc
    exact hnc
  have hNi:d.V.relIndex (normalizer (T:Set G))=36:=by
    change d.V.relIndex (normalizer ((d.V⊔d.D:Subgroup G):Set G)⊓normalizer (d.W:Set G))=36 at hni
    rw [←hT] at hni
    change d.V.relIndex (normalizer (T:Set G)⊓normalizer (d.W:Set G))=36 at hni
    rw [inf_eq_left.mpr hNle] at hni
    exact hni
  obtain ⟨hinv,hderived⟩:=h.cubic_line_oddKernel_inversion d.W hW hWH hfixed
  exact ⟨{
    toSourceData:=d
    line_card:=hW
    kernel_elementary:=hV
    kernel_card:=hVc
    fixed_quaternion:=hfixed
    quaternion_sylow:=hS
    odd_split:=hs
    odd_card:=hD
    odd_extraspecial:=he
    odd_cube:=hpow
    odd_fitting:=hfit
    odd_centralizer:=hCD
    odd_fixed:=h.cubic_line_oddKernel_fixed d.W hW hWH hfixed
    odd_inversion:=hinv
    odd_derived:=hderived
    intersection:=hcap
    intersection_card:=hcapc
    special_model:=hJ
    special_card:=hJc
    complement_card:=hK
    complement_le:=hKN
    complement_product:=hg
    complement_disjoint:=hd
    special_normalized:=hrJ
    sylow:=T
    sylow_eq:=hT
    sylow_card:=hQc
    sylow_center:=hcT
    common_normalizer:=hN
    normalizer_card:=hNc
    normalizer_index:=hNi
    maximum:=h.cubic_line_marked_maximum_abelian P actors ha hs hD he
  }⟩
end Theory.GroupTheory.Recognition.UnitaryFourThree.IsType
