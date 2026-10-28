module

public import Theory.GroupTheory.QuaternionCubicComplement
public import Theory.GroupTheory.Recognition.UnitaryFourThree.CubicLine.OddKernel
public import Theory.GroupTheory.Recognition.UnitaryFourThree.RootPair.PlaneSource
public import Theory.GroupTheory.Recognition.UnitaryFourThree.RootPair.ReflectedMarking.Source

/-!
# The original cubic-line complement of order forty-eight

Independent cubics on the two original quaternion factors and the reflected
rotation construct an actual SL₂(3) subgroup J and its index-two extension K.
The local order144 bound gives C_G(z) ∩ N_G(W)=WK. The previously proved
odd-core decomposition and D ∩ C_G(z)=W then give N_G(W)=DK and D ∩ K=1.

The marked theorem retains the same quaternion factor, cubic axes and rotation.
The final source theorem constructs the reflection marking from IsType itself.
No complement or local-group recognition premise is assumed.
Source: Aschbacher, Sporadic Groups (1994),45.8,printed pp245–246.
-/

public section
open Subgroup
namespace Theory.GroupTheory.Recognition.UnitaryFourThree
variable {G : Type*} [Group G] [Finite G] {z:G}
namespace IsType
variable (h:IsType z)
include h in
theorem cubic_line_complement_marked (P:Sylow 3 (centralizer z))
    (m:CubicNormalizer.ReflectedMarking z ((P:Subgroup (centralizer z)).map (centralizer z).subtype)) :
    ∃actors:QuaternionIndependentCubics h.toCentralizerHypothesis.factorData.leftCore
      h.toCentralizerHypothesis.factorData.rightCore,
    actors.A=(P:Subgroup (centralizer z)).map (centralizer z).subtype ∧
    let W:=zpowers (actors.x:G)
    let J:=h.toCentralizerHypothesis.factorData.rightCore⊔zpowers (actors.y:G)
    let K:=J⊔zpowers (m.s*m.t)
    Nat.card W=3 ∧
    Nonempty (J≃*Matrix.SpecialLinearGroup (Fin 2) (ZMod 3)) ∧ Nat.card J=24 ∧
    Nat.card K=48 ∧ K≤centralizer z⊓normalizer (W:Set G) ∧
    Disjoint W K ∧ centralizer z⊓normalizer (W:Set G)=W⊔K ∧
    normalizer (W:Set G)=CubicLine.oddKernel W⊔K ∧
    Disjoint (CubicLine.oddKernel W) K ∧
    m.s*m.t∈normalizer (J:Set G) ∧
    Nonempty ((core z⊓Subgroup.centralizer (W:Set G):Subgroup G)≃*QuaternionGroup 2) := by
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
  have hrC:r∈normalizer (d.rightCore:Set G):=
    (actors.normalizes_factors_of_inversion hB hC hi hcomm r (hnormal hr) hinv).2
  have hzC:z∈d.rightCore:=by
    have hh:z∈d.leftCore⊓d.rightCore:=d.core_intersection h.involution ▸ mem_zpowers z
    exact hh.2
  let W:=zpowers (actors.x:G)
  let J:=d.rightCore⊔zpowers (actors.y:G)
  let K:=J⊔zpowers r
  let S:=d.rightCore⊔zpowers r
  obtain ⟨hJmodel,hJcard,hKcard,hWK,hKN,hRJ⟩:=
    actors.complement_of_inverter hC hcomm z r h.involution hzC hrC m.rotation_square hinv
  have hWcard:Nat.card W=3:=by rw [Nat.card_zpowers,actors.x_order]
  have hAX:actors.A≤centralizer z:=ha ▸ map_subtype_le _
  have hWH:W≤centralizer z:=zpowers_le.mpr (hAX actors.x.property)
  have hCH:d.rightCore≤centralizer z:=(pCoreIn_le 2 d.right).trans (d.right_le.trans (map_subtype_le _))
  have hKH:K≤centralizer z:=sup_le (sup_le hCH (zpowers_le.mpr (hAX actors.y.property))) (zpowers_le.mpr hr)
  have hKL:K≤centralizer z⊓normalizer (W:Set G):=le_inf hKH hKN
  have hfixed:Nonempty ((core z⊓Subgroup.centralizer (W:Set G):Subgroup G)≃*QuaternionGroup 2):=by
    rw [←d.core_span h.involution,actors.fixed_core_left hB hi hcomm]
    exact hC
  obtain ⟨E,hEA,hE,hEH,hEQ,_⟩:=h.exists_plane_with_core_eight
  let : IsElementaryAbelian 2 E:=hEA
  have hbound:=h.cubic_line_normalizer_card_dvd W hWcard hWH hfixed E hEH hE hEQ
  have hWKcard:Nat.card (W⊔K:Subgroup G)=144:=by
    rw [card_sup_eq_mul_of_normalizes_of_disjoint W K hKN hWK,hWcard,hKcard]
  have hlocal:centralizer z⊓normalizer (W:Set G)=W⊔K:=by
    apply (eq_of_le_of_card_ge (sup_le (le_inf hWH W.le_normalizer) hKL) ?_).symm
    rw [hWKcard]
    exact Nat.le_of_dvd (by decide) hbound
  have hc3:(actors.actionC actors.y)^3=1:=by
    have hy3:actors.y^3=1:=Subtype.ext (actors.y_order ▸ pow_orderOf_eq_one (actors.y:G))
    rw [←map_pow,hy3,map_one]
  have hSmodel:Nonempty (S≃*QuaternionGroup 4):=
    quaternion_sixteen_of_cubic_inverter d.rightCore hC.some z r hzC h.involution hrC
      m.rotation_square (actors.actionC actors.y) hc3 actors.y_actionC_ne_one
      (actors.inverts_right_action r hrC (hinv actors.y actors.y.property))
  have hSK:S≤K:=sup_le (le_sup_left.trans le_sup_left) le_sup_right
  have hSL:S≤normalizer (W:Set G)⊓centralizer z:=le_inf (hSK.trans hKN) (hSK.trans hKH)
  have hzS:z∈S:=mem_sup_left hzC
  have hbound':Nat.card (normalizer (W:Set G)⊓centralizer z:Subgroup G)∣144:=by
    simpa only [inf_comm] using hbound
  obtain ⟨T,_,hTe⟩:=exists_sylow_of_quaternion_sixteen_local_bound (normalizer (W:Set G)) S z
    h.involution hzS hSL hSmodel.some hbound'
  have hsplit:=CubicLine.normalizer_oddCore_split W h.involution (hSL hzS).1 T hTe
  have hWD:W≤CubicLine.oddKernel W:=CubicLine.le_oddKernel W hWcard
  have hglobal:normalizer (W:Set G)=CubicLine.oddKernel W⊔K:=by
    rw [hsplit,inf_comm,hlocal,←sup_assoc,sup_eq_left.mpr hWD]
  have hDK:Disjoint (CubicLine.oddKernel W) K:=by
    apply disjoint_iff.mpr
    apply le_bot_iff.mp
    rw [←hWK.eq_bot]
    exact le_inf (fun x hx=>(h.cubic_line_oddKernel_fixed W hWcard hWH hfixed).le ⟨hx.1,hKH hx.2⟩) inf_le_right
  exact ⟨actors,ha,hWcard,hJmodel,hJcard,hKcard,hKL,hWK,hlocal,hglobal,hDK,hRJ,hfixed⟩

include h in
theorem original_cubic_line_complement (P:Sylow 3 (centralizer z)) :
    ∃W J K:Subgroup G,Nat.card W=3 ∧ W≤(P:Subgroup (centralizer z)).map (centralizer z).subtype ∧
      Nonempty (J≃*Matrix.SpecialLinearGroup (Fin 2) (ZMod 3)) ∧ Nat.card J=24 ∧
      J≤K ∧ Nat.card K=48 ∧ K≤centralizer z⊓normalizer (W:Set G) ∧
      Disjoint W K ∧ centralizer z⊓normalizer (W:Set G)=W⊔K ∧
      normalizer (W:Set G)=CubicLine.oddKernel W⊔K ∧ Disjoint (CubicLine.oddKernel W) K := by
  obtain ⟨m⟩:=h.original_reflected_marking P
  obtain ⟨actors,ha,hW,hJ,hJc,hK,hKL,hdis,hl,hg,hd,_,_⟩:=h.cubic_line_complement_marked P m
  refine ⟨_,_,_,hW,?_,hJ,hJc,le_sup_left,hK,hKL,hdis,hl,hg,hd⟩
  rw [←ha]
  exact zpowers_le.mpr actors.x.property
end IsType
end Theory.GroupTheory.Recognition.UnitaryFourThree
