module

public import Theory.GroupTheory.QuaternionCentralProductCubicLineNormalizer
public import Theory.GroupTheory.QuaternionCentralProductNineAction.FactorSwap
public import Theory.GroupTheory.Recognition.UnitaryFourThree.CubicNormalizer.QuaternionRotation
/-!
# The original factor swap and cubic-line normalizer bound

An elementary sixteen meeting the actual core in an eight supplies a
factor-swap actor. Combining the original local factors with the fixed
quaternion support of a cubic line gives the literal normalizer order bound.
The elementary sixteen is the earlier45.4 binary root-pair output.
Source: Aschbacher, *Sporadic Groups* (1994),45.8,printed p245.
-/

public section
open Subgroup
open scoped IsMulCommutative
namespace Theory.GroupTheory.Recognition.UnitaryFourThree
variable {G:Type*} [Group G] [Finite G] {z:G}
namespace IsType
variable (h:IsType z)
include h in
theorem exists_core_factor_swap_of_sixteen (E:Subgroup G) [IsElementaryAbelian 2 E]
    (hEH:E≤centralizer z) (hE:Nat.card E=16) (hEQ:Nat.card (E⊓core z:Subgroup G)=8) :
    let d:=h.toCentralizerHypothesis.factorData
    ∃s∈centralizer z,d.leftCore.map (MulAut.conj s).toMonoidHom=d.rightCore ∧
      d.rightCore.map (MulAut.conj s).toMonoidHom=d.leftCore := by
  let d:=h.toCentralizerHypothesis.factorData
  have hB:Nonempty (d.leftCore≃*QuaternionGroup 2):=⟨Factors.factorCoreEquiv d.left d.left_model.some⟩
  have hC:Nonempty (d.rightCore≃*QuaternionGroup 2):=⟨Factors.factorCoreEquiv d.right d.right_model.some⟩
  have hi:Nat.card (d.leftCore⊓d.rightCore:Subgroup G)=2:=by
    rw [d.core_intersection h.involution,Nat.card_zpowers,h.involution]
  have hc:∀b∈d.leftCore,∀c∈d.rightCore,b*c=c*b:=fun b hb c hc=>
    d.factors_commute h.involution b (pCoreIn_le 2 d.left hb) c (pCoreIn_le 2 d.right hc)
  have hnot:¬E≤core z:=by intro he;rw [inf_eq_left.mpr he,hE] at hEQ;omega
  obtain ⟨s,hsE,hsQ⟩:=SetLike.not_le_iff_exists.mp hnot
  have hswap:=quaternion_factors_swapped_of_fixed_elementary_eight d.leftCore d.rightCore
    (E⊓core z) hB hC hi hc
    (by rw [d.core_span h.involution,h.toCentralizerHypothesis.core_card])
    (by rw [d.core_span h.involution,h.toCentralizerHypothesis.centralizer_core];exact h.toCentralizerHypothesis.line_le_core)
    (by rw [d.core_span h.involution];exact inf_le_right) hEQ
    (fun u hu=>by
      exact congrArg Subtype.val (Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
        (IsElementaryAbelian.exponent_dvd_p (p:=2) (G:=E)) (⟨u,hu.1⟩:E))) s
    (by rw [d.core_span h.involution];exact CentralizerHypothesis.centralizer_normalizes_core (hEH hsE))
    (by rwa [d.core_span h.involution])
    (fun u hu=>congrArg Subtype.val (mul_comm (⟨s,hsE⟩:E) ⟨u,hu.1⟩))
  exact ⟨s,hEH hsE,hswap⟩

include h in
theorem cubic_line_normalizer_card_dvd (W:Subgroup G) (hW:Nat.card W=3)
    (hWH:W≤centralizer z)
    (hfixed:Nonempty ((core z⊓Subgroup.centralizer (W:Set G):Subgroup G)≃*QuaternionGroup 2))
    (E:Subgroup G) [IsElementaryAbelian 2 E]
    (hEH:E≤centralizer z) (hE:Nat.card E=16) (hEQ:Nat.card (E⊓core z:Subgroup G)=8) :
    Nat.card (centralizer z⊓normalizer (W:Set G):Subgroup G)∣144 := by
  let d:=h.toCentralizerHypothesis.factorData
  have hB:Nonempty (d.leftCore≃*QuaternionGroup 2):=⟨Factors.factorCoreEquiv d.left d.left_model.some⟩
  have hC:Nonempty (d.rightCore≃*QuaternionGroup 2):=⟨Factors.factorCoreEquiv d.right d.right_model.some⟩
  have hi:Nat.card (d.leftCore⊓d.rightCore:Subgroup G)=2:=by
    rw [d.core_intersection h.involution,Nat.card_zpowers,h.involution]
  have hc:∀b∈d.leftCore,∀c∈d.rightCore,b*c=c*b:=fun b hb c hc=>
    d.factors_commute h.involution b (pCoreIn_le 2 d.left hb) c (pCoreIn_le 2 d.right hc)
  have hQH:d.leftCore⊔d.rightCore≤centralizer z:=by
    rw [d.core_span h.involution];exact (pCoreIn_le 2 (residual z)).trans (map_subtype_le _)
  have hHN:centralizer z≤normalizer (d.leftCore⊔d.rightCore:Subgroup G):=by
    rw [d.core_span h.involution];exact CentralizerHypothesis.centralizer_normalizes_core
  obtain ⟨s,hs,hsB,hsC⟩:=h.exists_core_factor_swap_of_sixteen E hEH hE hEQ
  have hcases:=quaternion_subgroup_eq_factor d.leftCore d.rightCore
    (core z⊓Subgroup.centralizer (W:Set G)) hB hC hi hc hfixed
    (by rw [d.core_span h.involution];exact inf_le_left)
  rcases hcases with he|he
  · exact cubic_line_normalizer_card_dvd_of_quaternion_swap (centralizer z) d.rightCore d.leftCore W
      h.centralizer_card hC hB (by simpa only [inf_comm] using hi)
      (fun c hc' b hb=>(hc b hb c hc').symm)
      (by simpa only [sup_comm] using hQH) (by simpa only [sup_comm] using hHN)
      hW hWH (by simpa only [sup_comm,d.core_span h.involution] using he) s hs hsC hsB
  · exact cubic_line_normalizer_card_dvd_of_quaternion_swap (centralizer z) d.leftCore d.rightCore W
      h.centralizer_card hB hC hi hc hQH hHN hW hWH
      (by simpa only [d.core_span h.involution] using he) s hs hsB hsC
end IsType
end Theory.GroupTheory.Recognition.UnitaryFourThree
