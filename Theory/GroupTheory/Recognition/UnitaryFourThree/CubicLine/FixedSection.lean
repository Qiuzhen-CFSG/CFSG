module

public import Theory.GroupAction.QuaternionCubicSectionFixed
public import Theory.GroupTheory.CubicOutsideFixed
public import Theory.GroupTheory.Recognition.UnitaryFourThree.CubicLine.GeneralizedFitting

/-!
# The original cubic fixedspace and outside centralizer

The same independent cubic actors which construct the complement48 give
an actual nontrivial cubic on the quaternion factor. On the literal D/W,
the fixed-preimage bound identifies the fixed preimage with V∩D. Thus
for d in D outside V, C_V(d) lies in D. The order243 and odd-core split
are exactly the preceding source outputs; no module classification or
fixedspace conclusion is assumed.
Source: Aschbacher, Sporadic Groups (1994),45.8(2),printed p246.
-/

public section
open Subgroup

namespace Theory.GroupTheory.Recognition.UnitaryFourThree.IsType
variable {G:Type*} [Group G] [Finite G] {z:G} (h:IsType z)
include h in
private theorem marked_quaternion_fixed
    (actors:QuaternionIndependentCubics h.toCentralizerHypothesis.factorData.leftCore
      h.toCentralizerHypothesis.factorData.rightCore) :
    Nonempty ((core z⊓Subgroup.centralizer (zpowers (actors.x:G):Set G):Subgroup G)≃*QuaternionGroup 2) := by
  let d:=h.toCentralizerHypothesis.factorData
  have hB:Nonempty (d.leftCore≃*QuaternionGroup 2):=⟨Factors.factorCoreEquiv d.left d.left_model.some⟩
  have hi:Nat.card (d.leftCore⊓d.rightCore:Subgroup G)=2:=by
    rw [d.core_intersection h.involution,Nat.card_zpowers,h.involution]
  have hcomm:∀b∈d.leftCore,∀c∈d.rightCore,b*c=c*b:=fun b hb c hc=>
    d.factors_commute h.involution b (pCoreIn_le 2 d.left hb) c (pCoreIn_le 2 d.right hc)
  rw [←d.core_span h.involution,actors.fixed_core_left hB hi hcomm]
  exact ⟨Factors.factorCoreEquiv d.right d.right_model.some⟩

include h in
theorem cubic_line_marked_fixed_preimage (P:Sylow 3 (centralizer z))
    (actors:QuaternionIndependentCubics h.toCentralizerHypothesis.factorData.leftCore
      h.toCentralizerHypothesis.factorData.rightCore)
    (ha:actors.A=(P:Subgroup (centralizer z)).map (centralizer z).subtype)
    (hsplit:normalizer (zpowers (actors.x:G):Set G)=CubicLine.oddKernel (zpowers (actors.x:G))⊔
      (normalizer (zpowers (actors.x:G):Set G)⊓centralizer z))
    (hD:Nat.card (CubicLine.oddKernel (zpowers (actors.x:G)))=243) :
    ∀d∈CubicLine.oddKernel (zpowers (actors.x:G)),
      (actors.y:G)*d*(actors.y:G)⁻¹*d⁻¹∈zpowers (actors.x:G) ↔
        d∈CubicNormalizer.oddKernel ((P:Subgroup (centralizer z)).map (centralizer z).subtype) := by
  let X:=(P:Subgroup (centralizer z)).map (centralizer z).subtype
  let V:=CubicNormalizer.oddKernel X
  let d:=h.toCentralizerHypothesis.factorData
  let C:=d.rightCore
  let W:=zpowers (actors.x:G)
  let D:=CubicLine.oddKernel W
  let S:=normalizer (W:Set G)
  have hW:Nat.card W=3:=by rw [Nat.card_zpowers,actors.x_order]
  have hX:Nat.card X=9:=h.cubic_sylow_image_card P
  have hXH:X≤centralizer z:=map_subtype_le _
  have hWX:W≤X:=zpowers_le.mpr (ha.le actors.x.property)
  have hXV:X≤V:=CubicNormalizer.le_oddKernel X hX (h.toCentralizerHypothesis.cubic_centralizer X hX hXH)
  obtain ⟨hV,hVc⟩:=h.original_cubic_kernel_eighty_one P
  let : IsMulCommutative V:=hV.toIsMulCommutative
  have hVW:V≤Subgroup.centralizer (W:Set G):=(map_subtype_le _).trans (centralizer_le hWX)
  have hyV:(actors.y:G)∈V:=hXV (ha.le actors.y.property)
  have hCS:C≤S:=(le_centralizer_iff.mpr (zpowers_le.mpr actors.x_centralizes)).trans
    (centralizer_le_normalizer _)
  have hzC:z∈C:=by
    have hz:z∈d.leftCore⊓d.rightCore:=d.core_intersection h.involution ▸ mem_zpowers z
    exact hz.2
  have he:Nonempty (C≃*QuaternionGroup 2):=⟨Factors.factorCoreEquiv d.right d.right_model.some⟩
  have hfixed:=h.marked_quaternion_fixed actors
  have hc:(actors.actionC actors.y)^3=1:=by
    rw [←map_pow]
    have hy:actors.y^3=1:=Subtype.ext (actors.y_order ▸ pow_orderOf_eq_one (actors.y:G))
    rw [hy,map_one]
  let : (W.subgroupOf D).Normal:=CubicLine.line_normal W hW
  exact quaternion_cubic_section_fixed S C D W V
    (CubicLine.normalizer_normalizes_oddKernel W) le_rfl hCS he.some (actors.y:G)
    (centralizer_le_normalizer _ (hVW hyV)) hyV (actors.actionC actors.y) hc actors.y_actionC_ne_one
    (actors.actionC_apply actors.y) z hzC h.involution
    (h.cubic_line_oddKernel_inversion W hW (hWX.trans hXH) hfixed).1 hD hW
    (CubicLine.le_oddKernel W hW)
    (h.cubic_line_kernel_intersection X W hX hXH hW hWX hfixed hsplit hV hVc).2
end Theory.GroupTheory.Recognition.UnitaryFourThree.IsType

namespace Theory.GroupTheory.Recognition.UnitaryFourThree.IsType
variable {G:Type*} [Group G] [Finite G] {z:G} (h:IsType z)
include h in
theorem cubic_line_marked_outside_fixed (P:Sylow 3 (centralizer z))
    (actors:QuaternionIndependentCubics h.toCentralizerHypothesis.factorData.leftCore
      h.toCentralizerHypothesis.factorData.rightCore)
    (ha:actors.A=(P:Subgroup (centralizer z)).map (centralizer z).subtype)
    (hsplit:normalizer (zpowers (actors.x:G):Set G)=CubicLine.oddKernel (zpowers (actors.x:G))⊔
      (normalizer (zpowers (actors.x:G):Set G)⊓centralizer z))
    (hD:Nat.card (CubicLine.oddKernel (zpowers (actors.x:G)))=243) :
    let V:=CubicNormalizer.oddKernel ((P:Subgroup (centralizer z)).map (centralizer z).subtype)
    let D:=CubicLine.oddKernel (zpowers (actors.x:G))
    ∀d∈D,d∉V→V⊓Subgroup.centralizer ({d}:Set G)≤D := by
  let X:=(P:Subgroup (centralizer z)).map (centralizer z).subtype
  let V:=CubicNormalizer.oddKernel X
  let W:=zpowers (actors.x:G)
  have hX:=h.cubic_sylow_image_card P
  have hXH:X≤centralizer z:=map_subtype_le _
  have hXV:X≤V:=CubicNormalizer.le_oddKernel X hX (h.toCentralizerHypothesis.cubic_centralizer X hX hXH)
  have hWX:W≤X:=zpowers_le.mpr (ha.le actors.x.property)
  have hW:Nat.card W=3:=by rw [Nat.card_zpowers,actors.x_order]
  have hfixed:=h.marked_quaternion_fixed actors
  obtain ⟨hV,hVc⟩:=h.original_cubic_kernel_eighty_one P
  have hcap:= (h.cubic_line_kernel_intersection X W hX hXH hW hWX hfixed hsplit hV hVc).2
  have hcomm:= (h.cubic_line_oddKernel_inversion W hW (hWX.trans hXH) hfixed).2
  exact cubic_outside_fixed_of_preimage V (CubicLine.oddKernel W) W (actors.y:G)
    (hXV (ha.le actors.y.property)) (h.original_cubic_kernel_eighty_one P).2 hcap
    (((map_subtype_le _:V≤Subgroup.centralizer (X:Set G)).trans (centralizer_le hWX)).trans
      (centralizer_le_normalizer _)) hcomm
    (fun d hd hh=>(h.cubic_line_marked_fixed_preimage P actors ha hsplit hD d hd).mp hh)
end Theory.GroupTheory.Recognition.UnitaryFourThree.IsType
