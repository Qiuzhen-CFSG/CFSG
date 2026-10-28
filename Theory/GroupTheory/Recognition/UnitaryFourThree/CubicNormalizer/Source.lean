module

public import Theory.GroupTheory.Recognition.UnitaryFourThree.CubicNormalizer.OddKernel
public import Theory.GroupTheory.QuaternionIndependentCubicCentralizer
/-!
# The original cubic centralizer and its odd kernel

The genuine marked SL₂(3) factors supply independent cubic actions on the
extraspecial core. Their centralizer in the involution centralizer is X⟨z⟩,
so the canonical odd kernel has fixed subgroup X and an inverted abelian
quotient. No additional centralizer or local-model premise is retained.

Source: Aschbacher, *Sporadic Groups* (1994), Lemma 45.7, printed p.245.
-/

@[expose] public section
open Subgroup
namespace Theory.GroupTheory.Recognition.UnitaryFourThree
variable {G : Type*} [Group G] [Finite G] {z : G}
namespace CentralizerHypothesis
variable (h : CentralizerHypothesis z) (X : Subgroup G)
  (hX : Nat.card X=9) (hXH : X≤centralizer z)
include h hX hXH in
theorem cubic_centralizer : centralizer z ⊓ Subgroup.centralizer (X:Set G)=X⊔zpowers z := by
  let d := h.factorData
  have hB : Nonempty (d.leftCore≃*QuaternionGroup 2) :=
    ⟨Factors.factorCoreEquiv d.left d.left_model.some⟩
  have hC : Nonempty (d.rightCore≃*QuaternionGroup 2) :=
    ⟨Factors.factorCoreEquiv d.right d.right_model.some⟩
  have hi : Nat.card (d.leftCore⊓d.rightCore : Subgroup G)=2 := by
    rw [d.core_intersection h.involution,Nat.card_zpowers,h.involution]
  have hc : ∀b∈d.leftCore,∀c∈d.rightCore,b*c=c*b := fun b hb c hc=>
    d.factors_commute h.involution b (pCoreIn_le 2 d.left hb) c (pCoreIn_le 2 d.right hc)
  have hself : Subgroup.centralizer (d.leftCore⊔d.rightCore : Subgroup G)≤d.leftCore⊔d.rightCore := by
    rw [d.core_span h.involution,h.centralizer_core]
    exact h.line_le_core
  have hnormal : centralizer z≤normalizer (d.leftCore⊔d.rightCore : Subgroup G) := by
    rw [d.core_span h.involution]
    exact centralizer_normalizes_core
  obtain ⟨actors,ha⟩ := independent_cubics_of_nine_subgroup d.leftCore d.rightCore X
    hB hC hi hc hself hX (hXH.trans hnormal)
  apply le_antisymm
  · have hh := actors.normalizer_inf_centralizer_le hB hC hi hc
    rw [ha,d.core_span h.involution,h.centralizer_core] at hh
    exact (inf_le_inf hnormal le_rfl).trans (by simpa only [d.core_span h.involution] using hh)
  · let : IsMulCommutative X := IsPGroup.isMulCommutative_of_card_eq_prime_sq (p:=3) hX
    apply sup_le
    · apply le_inf hXH
      intro x hx y hy
      exact congrArg Subtype.val ((IsMulCommutative.is_comm (M:=X)).comm (⟨y,hy⟩:X) ⟨x,hx⟩)
    · apply le_inf
      · exact zpowers_le.mpr (mem_centralizer_singleton_iff.mpr rfl)
      · exact zpowers_le.mpr (fun x hx=>mem_centralizer_singleton_iff.mp (hXH hx))

include h hX hXH in
theorem cubic_centralizer_split :
    Subgroup.centralizer (X:Set G)=CubicNormalizer.oddKernel X⊔zpowers z :=
  CubicNormalizer.centralizer_split h X hX hXH (h.cubic_centralizer X hX hXH)
include h hX hXH in
theorem cubic_oddKernel_fixed : CubicNormalizer.oddKernel X⊓centralizer z=X :=
  CubicNormalizer.fixed_oddKernel h X hX hXH (h.cubic_centralizer X hX hXH)
include h hX hXH in
theorem cubic_oddKernel_inversion :
    (∀v∈CubicNormalizer.oddKernel X,z*v*z⁻¹*v∈X) ∧
      ⁅CubicNormalizer.oddKernel X,CubicNormalizer.oddKernel X⁆≤X :=
  CubicNormalizer.oddKernel_quotient_inversion h X hX hXH (h.cubic_centralizer X hX hXH)
end CentralizerHypothesis
end Theory.GroupTheory.Recognition.UnitaryFourThree
