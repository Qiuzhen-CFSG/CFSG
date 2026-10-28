module

public import Theory.GroupTheory.Recognition.UnitaryFourThree.CubicNormalizer.Frattini
public import Theory.ElementaryAbelian.Injective
/-!
# Elementary odd local subgroups

Odd subgroups of the marked involution centralizer are elementary ternary: their orders divide nine, and independent quaternion cubics settle the order-nine case. The statement transports to each fused involution centralizer.

Source: Aschbacher, *Sporadic Groups* (1994), Lemma45.7, printed p.245.
-/

@[expose] public section
open Subgroup
namespace Theory.GroupTheory.Recognition.UnitaryFourThree
variable {G : Type*} [Group G] [Finite G] {z:G}
namespace CentralizerHypothesis
variable (h : CentralizerHypothesis z) (X : Subgroup G)
  (hX : Nat.card X=9) (hXH : X≤centralizer z)
include h hX hXH in
theorem nine_elementary : IsElementaryAbelian 3 X := by
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
  exact ha ▸ actors.elementary

end CentralizerHypothesis
namespace IsType
variable (h : IsType z)
include h in
theorem odd_subgroup_elementary (Y : Subgroup G) (ho : Odd (Nat.card Y))
    (hY : Y≤centralizer z) : IsElementaryAbelian 3 Y := by
  have hd := card_dvd_of_le hY
  rw [h.centralizer_card] at hd
  have hd9 : Nat.card Y∣9 := (ho.coprime_two_right.pow_right 7).dvd_mul_left.mp hd
  by_cases h9 : Nat.card Y=9
  · exact h.toCentralizerHypothesis.nine_elementary Y h9 hY
  have hd3 : Nat.card Y∣3 := by
    have hh := Nat.mem_divisors.mpr ⟨hd9,(by decide : 9≠0)⟩
    have he : Nat.divisors 9={1,3,9} := by decide
    simp only [he,Finset.mem_insert,Finset.mem_singleton] at hh
    rcases hh with hh | hh | hh
    · rw [hh]; exact one_dvd _
    · rw [hh]
    · exact (h9 hh).elim
  let : IsCyclic Y := isCyclic_of_card_dvd_prime (p:=3) hd3
  exact { toIsMulCommutative := inferInstance
          exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr
            (fun y=>orderOf_dvd_iff_pow_eq_one.mp ((orderOf_dvd_natCard y).trans hd3)) }

include h in
theorem odd_subgroup_elementary_of_isConj (t : G) (ht : IsConj z t)
    (Y : Subgroup G) (ho : Odd (Nat.card Y))
    (hY : Y≤Subgroup.centralizer ({t}:Set G)) : IsElementaryAbelian 3 Y := by
  obtain ⟨g,hg⟩ := isConj_iff.mp ht
  let e := MulAut.conj g⁻¹
  have he : e t=z := by rw [←hg]; simp [e,mul_assoc]
  have hYZ : Y.map e.toMonoidHom≤centralizer z := by
    rintro x ⟨y,hy,rfl⟩
    apply mem_centralizer_singleton_iff.mpr
    change e y*z=z*e y
    rw [←he,←map_mul,←map_mul]
    exact congrArg e (mem_centralizer_singleton_iff.mp (hY hy))
  have hodd : Odd (Nat.card (Y.map e.toMonoidHom)) := by
    rwa [card_map_of_injective e.injective]
  let : IsElementaryAbelian 3 (Y.map e.toMonoidHom) := h.odd_subgroup_elementary _ hodd hYZ
  let f := Y.equivMapOfInjective e.toMonoidHom e.injective
  exact IsElementaryAbelian.of_injective f.toMonoidHom f.injective
end IsType
end Theory.GroupTheory.Recognition.UnitaryFourThree
