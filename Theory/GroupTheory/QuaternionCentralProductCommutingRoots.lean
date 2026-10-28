module
public import Theory.GroupTheory.QuaternionCentralFactorRoots
public import Theory.GroupTheory.QuaternionCentralProductIntrinsic

/-!
# Commuting square roots in a quaternion central supplement

Let U be a central product of two quaternion eights and Q = U C_Q(U).
The central involution of U has a square root in U commuting with every
prescribed element of Q. Choose the root in one quaternion factor, then
use the central supplement to preserve commutation.

Source application: Aschbacher--Smith, Quasithin Groups, the final
Frattini contradiction in 14.3.21(2), printed p.998.
-/

public noncomputable section
open Subgroup
namespace Theory.GroupTheory
variable {G : Type*} [Group G] [Finite G]

theorem commuting_square_root_of_quaternion_supplement
    (U Q : Subgroup G) (d : QuaternionCentralProductData U)
    (hQ : Q = U ⊔ (Q ⊓ centralizer (U : Set G)))
    (z : U) (hz : orderOf z = 2) (hzc : z ∈ center U)
    (a : G) (ha : a ∈ Q) :
    ∃ x ∈ U, x ^ 2 = (z : G) ∧ Commute x a := by
  have hspan : d.left ⊔ centralizer (d.left : Set U) = ⊤ := by
    apply top_unique
    rw [← d.span]
    apply sup_le_sup_left
    intro c hc b hb
    exact d.commute b hb c hc
  have hzB : z ∈ d.left := (d.center_eq.le hzc).1
  obtain ⟨_,hroot⟩ := quaternion_central_factor_involution_roots
    d.left d.left_model.some hspan ⟨z,hzB⟩ ((orderOf_coe _).symm.trans hz)
  have hnorm : Q ⊓ centralizer (U : Set G) ≤ normalizer (U : Set G) :=
    inf_le_right.trans (centralizer_le_normalizer _)
  rw [hQ, ← SetLike.mem_coe,
    coe_mul_of_right_le_normalizer_left U _ hnorm] at ha
  obtain ⟨u,hu,c,hc,rfl⟩ := ha
  obtain ⟨x,hx,hxu⟩ := hroot ⟨u,hu⟩
  refine ⟨(x:U),x.val.property,congrArg Subtype.val hx,?_⟩
  exact (hxu.map U.subtype).mul_right (hc.2 (x:U) x.val.property)
end Theory.GroupTheory
