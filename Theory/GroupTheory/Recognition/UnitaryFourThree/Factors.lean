module

public import Theory.GroupTheory.Recognition.UnitaryFourThree.Defs
public import Theory.SpecificGroups.SL2.ThreeResidualCore
public import Theory.GroupTheory.CentralPResidualCommutator
public import Theory.GroupTheory.NormalizedSupCard

/-!
# The actual SL₂(3) factors in a group of type U₄(3)

The normal factors from Hypothesis 45.1 commute. Their commutators lie in
 the common central involution, and two-perfectness of SL₂(3) kills each
 resulting central binary commutator map. Their literal join therefore has
 order 288. These are source deductions, not recognition assumptions.

Source: Aschbacher, *Sporadic Groups* (1994), Lemma 45.2, printed p.242.
-/

@[expose] public section
open Subgroup GLS3.Chapter5.SchurPresentation
open scoped commutatorElement
namespace Theory.GroupTheory.Recognition.UnitaryFourThree
variable {G : Type*} [Group G] {z : G}

structure Factors (z : G) where
  left : Subgroup G
  right : Subgroup G
  span : left ⊔ right = residual z
  normal_left : (left.subgroupOf (residual z)).Normal
  normal_right : (right.subgroupOf (residual z)).Normal
  left_model : Nonempty (left ≃* SL23)
  right_model : Nonempty (right ≃* SL23)
  intersection : left ⊓ right = zpowers z

noncomputable def CentralizerHypothesis.factorData (h : CentralizerHypothesis z) : Factors z := by
  choose A B h using h.factors
  exact ⟨A,B,h.1,h.2.1,h.2.2.1,h.2.2.2.1,h.2.2.2.2.1,h.2.2.2.2.2⟩

namespace Factors
variable (d : Factors z)

theorem left_le : d.left ≤ residual z := d.span ▸ le_sup_left
theorem right_le : d.right ≤ residual z := d.span ▸ le_sup_right

theorem left_normalized : residual z ≤ normalizer (d.left : Set G) :=
  (normal_subgroupOf_iff_le_normalizer d.left_le).mp d.normal_left

theorem right_normalized : residual z ≤ normalizer (d.right : Set G) :=
  (normal_subgroupOf_iff_le_normalizer d.right_le).mp d.normal_right

theorem factors_commute (hz : orderOf z = 2) :
    ∀ a ∈ d.left, ∀ b ∈ d.right, a * b = b * a := by
  let Z := (zpowers z).subgroupOf d.left
  have hzl : zpowers z ≤ d.left := d.intersection ▸ inf_le_left
  have hzcard : Nat.card (zpowers z) = 2 := by rw [Nat.card_zpowers, hz]
  have hp : IsPGroup 2 Z := (IsPGroup.of_card (n := 1) hzcard).comap_subtype
  have hc : Z ≤ center d.left := by
    intro x hx
    apply mem_center_iff.mpr
    intro a
    apply Subtype.ext
    have ha : (a : G) ∈ centralizer z := (map_subtype_le _ : residual z ≤ centralizer z)
      (d.left_le a.property)
    obtain ⟨n, hn⟩ := mem_zpowers_iff.mp hx
    change (a : G) * (x : G) = (x : G) * (a : G)
    change z ^ n = (x : G) at hn
    rw [← hn]
    exact (show Commute (a : G) z from mem_centralizer_singleton_iff.mp ha).zpow_right n
  have hperf : IsPPerfect 2 d.left :=
    sl23_twoPerfect.of_surjective d.left_model.some.symm.toMonoidHom
      d.left_model.some.symm.surjective
  have hcomm : ⁅d.left,d.right⁆ ≤ zpowers z := by
    rw [← d.intersection]
    exact le_inf
      (le_normalizer_iff_commutator_le_left.mp (d.right_le.trans d.left_normalized))
      (le_normalizer_iff_commutator_le_right.mp (d.left_le.trans d.right_normalized))
  intro a ha b hb
  exact (commute_of_central_p_commutator_of_isPPerfect d.left Z hperf hp hc b (by
    intro x
    rw [show Z.map d.left.subtype = zpowers z from map_subgroupOf_eq_of_le hzl]
    exact hcomm (commutator_mem_commutator x.property hb)) a ha).symm

include d in
theorem residual_card [Finite G] (hz : orderOf z = 2) : Nat.card (residual z) = 288 := by
  have hc := card_mul_eq_card_inf_mul_card_sup_of_normalizes d.left d.right
    (d.right_le.trans d.left_normalized)
  have hl : Nat.card d.left = 24 := (Nat.card_congr d.left_model.some.toEquiv).trans sl23_card_eq
  have hr : Nat.card d.right = 24 := (Nat.card_congr d.right_model.some.toEquiv).trans sl23_card_eq
  rw [hl,hr,d.intersection,Nat.card_zpowers,hz,d.span] at hc
  omega

end Factors
end Theory.GroupTheory.Recognition.UnitaryFourThree
