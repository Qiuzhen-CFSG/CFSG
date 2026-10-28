module
public import Theory.GroupTheory.Recognition.UnitaryFourThree.RootPair.PlaneCentralizers
public import Theory.GroupTheory.QuaternionCentralProductCubicStabilizer

/-!
# A genuine cubic point stabilizer for the source plane

The actual order-nine subgroup of the involution centralizer acts by
independent cubic automorphisms on its quaternion factors. Its orbit on
at most six elementary eights has a nontrivial stabilizer. Since the
centralizer of the plane's core eight is the plane, this cubic also
normalizes the original plane and fixes z.
Source: Aschbacher, Sporadic Groups (1994),45.6, printed p.244.
-/

public section
open Subgroup
namespace Theory.GroupTheory.Recognition.UnitaryFourThree
variable {G:Type*} [Group G] [Finite G] {z:G}
namespace RootPair
variable (P:RootPair z)

theorem exists_cubic_plane_stabilizer (h:IsType z) (V:Subgroup G)
    (hV:V≤P.T ∧ IsElementaryAbelian 2 V ∧ Nat.card V=16) :
    ∃a∈centralizer z⊓normalizer (V:Set G),orderOf a=3 := by
  let := hV.2.1
  let d:=h.toCentralizerHypothesis.factorData
  let S:Sylow 3 (centralizer z):=Classical.choice inferInstance
  let X:Subgroup G := (S:Subgroup (centralizer z)).map (centralizer z).subtype
  have hX:Nat.card X=9 := by
    rw [card_map_of_injective (centralizer z).subtype_injective,S.card_eq_multiplicity,h.centralizer_card]
    decide +kernel
  have hXH:X≤centralizer z := map_subtype_le _
  have hB:Nonempty (d.leftCore≃*QuaternionGroup 2) := ⟨Factors.factorCoreEquiv d.left d.left_model.some⟩
  have hC:Nonempty (d.rightCore≃*QuaternionGroup 2) := ⟨Factors.factorCoreEquiv d.right d.right_model.some⟩
  have hi:Nat.card (d.leftCore⊓d.rightCore:Subgroup G)=2 := by
    rw [d.core_intersection h.involution,Nat.card_zpowers,h.involution]
  have hc:∀b∈d.leftCore,∀c∈d.rightCore,b*c=c*b := fun b hb c hc=>
    d.factors_commute h.involution b (pCoreIn_le 2 d.left hb) c (pCoreIn_le 2 d.right hc)
  have hself:Subgroup.centralizer ((d.leftCore⊔d.rightCore:Subgroup G):Set G)≤d.leftCore⊔d.rightCore := by
    rw [d.core_span h.involution,h.toCentralizerHypothesis.centralizer_core]
    exact h.toCentralizerHypothesis.line_le_core
  have hn:centralizer z≤normalizer ((d.leftCore⊔d.rightCore:Subgroup G):Set G) := by
    rw [d.core_span h.involution]
    exact CentralizerHypothesis.centralizer_normalizes_core
  obtain ⟨actors,ha⟩:=independent_cubics_of_nine_subgroup d.leftCore d.rightCore X hB hC hi hc hself hX (hXH.trans hn)
  let U:=V⊓core z
  let : IsElementaryAbelian 2 U := IsElementaryAbelian.of_injective
    (inclusion (show U≤V from inf_le_left)) (inclusion_injective _)
  have hU:Nat.card U=8 := P.plane_inf_core_card h V hV
  have hUQ:U≤d.leftCore⊔d.rightCore := (d.core_span h.involution) ▸ inf_le_right
  obtain ⟨a,hane,han⟩:=actors.exists_nontrivial_normalizing hB hC hi hc U hU hUQ
  have hanV:(a:G)∈normalizer (V:Set G) := by
    rw [←P.plane_core_eight_centralizer h V hV]
    exact normalizer_le_normalizer_centralizer U han
  let := actors.elementary
  have ha3:(a:G)^3=1 := elemPow_eq_one_of_isElementaryAbelian (a:G) a.property
  refine ⟨a,⟨hXH (ha ▸ a.property),hanV⟩,orderOf_eq_prime ha3 ?_⟩
  exact fun he=>hane (Subtype.ext he)
end RootPair
end Theory.GroupTheory.Recognition.UnitaryFourThree
