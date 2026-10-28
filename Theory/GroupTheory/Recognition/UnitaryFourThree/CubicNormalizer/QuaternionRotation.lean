module

public import Theory.GroupTheory.QuaternionCubicInverterExtension
public import Theory.GroupTheory.QuaternionCentralProductInvertingCubics
public import Theory.GroupTheory.Recognition.UnitaryFourThree.CubicNormalizer.MarkedKernel

/-!
# The original cubic axis and its quaternion-sixteen normalizer subgroup

The two reflected actors give a rotation whose square is z. It inverts the
whole original Sylow nine and therefore preserves its two quaternion
supports. Adjoining that rotation to the second support constructs Q₁₆
inside the original normalizer of the first cubic axis. The fixed core of
that axis has order8. No quaternion ambient Sylow premise is used here.

The reflected actor marking is the earlier45.3–45.6 source family.
Source: Aschbacher, *Sporadic Groups* (1994),45.8,printed p245.
-/

public section
open Subgroup
namespace Theory.GroupTheory.Recognition.UnitaryFourThree
variable {G:Type*} [Group G] [Finite G] {z:G}
namespace CubicNormalizer.ReflectedMarking
variable {X:Subgroup G} (m:ReflectedMarking z X)
omit [Finite G] in
theorem rotation_square : (m.s*m.t)^2=z := by
  have hs:m.s⁻¹=m.s:=inv_eq_of_mul_eq_one_left (by simpa only [pow_two,m.s_order] using pow_orderOf_eq_one m.s)
  have ht:m.t*m.t=1:=by simpa only [pow_two,m.t_order] using pow_orderOf_eq_one m.t
  calc
    (m.s*m.t)^2=(m.s*m.t*m.s⁻¹)*m.t := by rw [hs,pow_two]; group
    _ = (m.t*z)*m.t := by rw [m.reflection_conjugation]
    _ = z := by rw [←m.zt_commute.eq, mul_assoc,ht,mul_one]
omit [Finite G] in
theorem rotation_centralizes : m.s*m.t∈centralizer z := by
  apply mem_centralizer_singleton_iff.mpr
  simpa only [m.rotation_square] using (Commute.self_pow (m.s*m.t) 2).eq
end CubicNormalizer.ReflectedMarking
namespace IsType
variable (h:IsType z)
include h in
theorem exists_cubic_line_quaternion_sixteen_marked (P:Sylow 3 (centralizer z))
    (m:CubicNormalizer.ReflectedMarking z ((P:Subgroup (centralizer z)).map (centralizer z).subtype)) :
    ∃W S:Subgroup G,Nat.card W=3 ∧ W≤(P:Subgroup (centralizer z)).map (centralizer z).subtype ∧
      Nonempty ((core z⊓Subgroup.centralizer (W:Set G):Subgroup G)≃*QuaternionGroup 2) ∧
      S≤normalizer (W:Set G)⊓centralizer z ∧ z∈S ∧ Nonempty (S≃*QuaternionGroup 4) := by
  let X:=(P:Subgroup (centralizer z)).map (centralizer z).subtype
  let d:=h.toCentralizerHypothesis.factorData
  have hB:Nonempty (d.leftCore≃*QuaternionGroup 2):=⟨Factors.factorCoreEquiv d.left d.left_model.some⟩
  have hC:Nonempty (d.rightCore≃*QuaternionGroup 2):=⟨Factors.factorCoreEquiv d.right d.right_model.some⟩
  have hi:Nat.card (d.leftCore⊓d.rightCore:Subgroup G)=2:=by
    rw [d.core_intersection h.involution,Nat.card_zpowers,h.involution]
  have hcomm:∀b∈d.leftCore,∀c∈d.rightCore,b*c=c*b:=fun b hb c hc=>
    d.factors_commute h.involution b (pCoreIn_le 2 d.left hb) c (pCoreIn_le 2 d.right hc)
  have hself:Subgroup.centralizer (d.leftCore⊔d.rightCore:Subgroup G)≤d.leftCore⊔d.rightCore:=by
    rw [d.core_span h.involution,h.toCentralizerHypothesis.centralizer_core]
    exact h.toCentralizerHypothesis.line_le_core
  have hnormal:centralizer z≤normalizer (d.leftCore⊔d.rightCore:Subgroup G):=by
    rw [d.core_span h.involution]
    exact CentralizerHypothesis.centralizer_normalizes_core
  obtain ⟨actors,ha⟩:=independent_cubics_of_nine_subgroup d.leftCore d.rightCore X hB hC hi hcomm
    hself (h.cubic_sylow_image_card P) ((map_subtype_le _).trans hnormal)
  let r:=m.s*m.t
  have hr:r∈centralizer z:=m.rotation_centralizes
  have hinv:∀x∈actors.A,r*x*r⁻¹=x⁻¹:=by rw [ha]; exact m.rotation_inverts
  have hrC: r∈normalizer (d.rightCore:Set G):=
    (actors.normalizes_factors_of_inversion hB hC hi hcomm r (hnormal hr) hinv).2
  let W:=zpowers (actors.x:G)
  let S:=d.rightCore⊔zpowers r
  have hzC:z∈d.rightCore:=by
    have hh:z∈d.leftCore⊓d.rightCore:=d.core_intersection h.involution ▸ mem_zpowers z
    exact hh.2
  have hc3:(actors.actionC actors.y)^3=1:=by
    have hy3:actors.y^3=1:=Subtype.ext (actors.y_order ▸ pow_orderOf_eq_one (actors.y:G))
    rw [←map_pow,hy3,map_one]
  have hSmodel:Nonempty (S≃*QuaternionGroup 4):=
    quaternion_sixteen_of_cubic_inverter d.rightCore hC.some z r hzC h.involution hrC
      m.rotation_square (actors.actionC actors.y) hc3 actors.y_actionC_ne_one
      (actors.inverts_right_action r hrC (hinv actors.y actors.y.property))
  refine ⟨W,S,?_,?_,?_,?_,mem_sup_left hzC,hSmodel⟩
  · rw [Nat.card_zpowers,actors.x_order]
  · change W≤X
    rw [←ha]
    exact zpowers_le.mpr actors.x.property
  · rw [←d.core_span h.involution,actors.fixed_core_left hB hi hcomm]
    exact hC
  · apply le_inf
    · apply sup_le
      · apply (le_centralizer_iff.mp (zpowers_le.mpr actors.x_centralizes)).trans (centralizer_le_normalizer _)
      · apply zpowers_le.mpr
        apply mem_normalizer_iff_map_conj_eq.mpr
        rw [MonoidHom.map_zpowers]
        change zpowers (r*(actors.x:G)*r⁻¹)=zpowers (actors.x:G)
        rw [hinv actors.x actors.x.property,zpowers_inv]
    · exact sup_le ((pCoreIn_le 2 d.right).trans (d.right_le.trans (map_subtype_le _))) (zpowers_le.mpr hr)
include h in
theorem exists_cubic_line_quaternion_sixteen (P:Sylow 3 (centralizer z))
    (m:CubicNormalizer.ReflectedMarking z ((P:Subgroup (centralizer z)).map (centralizer z).subtype)) :
    ∃W S:Subgroup G,Nat.card W=3 ∧ W≤(P:Subgroup (centralizer z)).map (centralizer z).subtype ∧
      Nat.card (core z⊓Subgroup.centralizer (W:Set G):Subgroup G)=8 ∧
      S≤normalizer (W:Set G)⊓centralizer z ∧ z∈S ∧ Nonempty (S≃*QuaternionGroup 4) := by
  obtain ⟨W,S,hW,hWX,⟨e⟩,hS,hzS,he⟩:=h.exists_cubic_line_quaternion_sixteen_marked P m
  refine ⟨W,S,hW,hWX,?_,hS,hzS,he⟩
  rw [Nat.card_congr e.toEquiv,Nat.card_eq_fintype_card,QuaternionGroup.card]

end IsType
end Theory.GroupTheory.Recognition.UnitaryFourThree
