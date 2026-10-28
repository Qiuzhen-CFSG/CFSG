module
public import Theory.GroupTheory.QuaternionSixteenMarkedGenerator
public import Theory.GroupTheory.Recognition.UnitaryFourThree.CubicLine.Complement.Action

/-!
# The actual quaternion frame in the source complement

The source reflected marking preserves the right quaternion factor and inverts
its nontrivial cubic action. Its square is the original central involution,
so the existing Q₁₆ extension theorem applies to these literal subgroups.
The marked-generator theorem then chooses a in the original complement,
retaining r=s*t and enumerating the actual right factor by quaternion words.

Source: Aschbacher, *Sporadic Groups* (1994), 45.8 and 45.11, pp.245–248.
-/

public section
open Subgroup
namespace Theory.GroupTheory.Recognition.UnitaryFourThree.CubicGeometry.SourceConfiguration
variable {G : Type*} [Group G] [Finite G] {z : G} {h : IsType z}
  {P : Sylow 3 (centralizer z)} (c : SourceConfiguration h P)

theorem exists_complement_quaternion_generator :
    ∃ a : G, a∈c.K ∧ a^4=z ∧
      (c.marking.s*c.marking.t)*a=a⁻¹*(c.marking.s*c.marking.t) ∧
      (∀ k : Fin 8, quaternionMarkedWord a (c.marking.s*c.marking.t) z k ∈
        h.toCentralizerHypothesis.factorData.rightCore) ∧
      (∀ x∈h.toCentralizerHypothesis.factorData.rightCore, ∃ k : Fin 8,
        x=quaternionMarkedWord a (c.marking.s*c.marking.t) z k) := by
  let d := h.toCentralizerHypothesis.factorData
  let r := c.marking.s*c.marking.t
  have hB : Nonempty (d.leftCore≃*QuaternionGroup 2) :=
    ⟨Factors.factorCoreEquiv d.left d.left_model.some⟩
  have hC : Nonempty (d.rightCore≃*QuaternionGroup 2) :=
    ⟨Factors.factorCoreEquiv d.right d.right_model.some⟩
  have hi : Nat.card (d.leftCore⊓d.rightCore : Subgroup G)=2 := by
    rw [d.core_intersection h.involution,Nat.card_zpowers,h.involution]
  have hcomm : ∀ b∈d.leftCore,∀ v∈d.rightCore,b*v=v*b := fun b hb v hv =>
    d.factors_commute h.involution b (pCoreIn_le 2 d.left hb) v (pCoreIn_le 2 d.right hv)
  have hnormal : centralizer z≤normalizer (d.leftCore⊔d.rightCore : Subgroup G) := by
    rw [d.core_span h.involution]
    exact CentralizerHypothesis.centralizer_normalizes_core
  have hinv : ∀ x∈c.actors.A,r*x*r⁻¹=x⁻¹ := by
    rw [c.actors_eq]
    exact c.marking.rotation_inverts
  have hrC : r∈normalizer (d.rightCore : Set G) :=
    (c.actors.normalizes_factors_of_inversion hB hC hi hcomm r
      (hnormal c.marking.rotation_centralizes) hinv).2
  have hzC : z∈d.rightCore := (d.core_intersection h.involution ▸ mem_zpowers z).2
  have hc3 : (c.actors.actionC c.actors.y)^3=1 := by
    have hy3 : c.actors.y^3=1 := Subtype.ext (c.actors.y_order ▸ pow_orderOf_eq_one (c.actors.y:G))
    rw [←map_pow,hy3,map_one]
  obtain ⟨E⟩ := quaternion_sixteen_of_cubic_inverter d.rightCore hC.some z r hzC
    h.involution hrC c.marking.rotation_square (c.actors.actionC c.actors.y) hc3
    c.actors.y_actionC_ne_one (c.actors.inverts_right_action r hrC (hinv c.actors.y c.actors.y.property))
  obtain ⟨a,ha,haz,har,hm,hs⟩ := exists_marked_quaternion_generator d.rightCore hC.some
    z r hzC h.involution c.marking.rotation_square E
  refine ⟨a,?_,haz,har,hm,hs⟩
  exact (show d.rightCore⊔zpowers r ≤ c.K from
    sup_le (le_sup_left.trans le_sup_left) le_sup_right) ha
end Theory.GroupTheory.Recognition.UnitaryFourThree.CubicGeometry.SourceConfiguration
