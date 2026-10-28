module
public import Theory.Representation.BinaryPrimeDisplacement.Quotient
public import Theory.SpecificGroups.Alternating.FiveInvolutionFusion
import Mathlib.Tactic.FinCases

/-!
# Involution displacement above an alternating-five quotient

A quotient-visible involution has a commutator whose quotient has order five.
On a faithful binary module this commutator moves at least four dimensions.
The commutator rank inequality therefore forces the involution to move at
least two dimensions, even before removing the odd action kernel.

Source: Niles, Pushing-up in finite groups (1979), Lemma 2.8, pp.32–33.
-/
public section
open Subgroup Representation Representation.BinaryOffender
namespace Representation.BinaryOffender
private def t : alternatingGroup (Fin 5) :=
  ⟨Equiv.swap 0 1 * Equiv.swap 2 3, by rw [Equiv.Perm.mem_alternatingGroup]; decide⟩
private def u : alternatingGroup (Fin 5) :=
  ⟨Equiv.swap 1 2 * Equiv.swap 3 4, by rw [Equiv.Perm.mem_alternatingGroup]; decide⟩
private theorem t_order : orderOf t=2 := orderOf_eq_prime (by decide) (by decide)
private theorem comm_order : orderOf (t*u*t⁻¹*u⁻¹)=5 := by
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  have ht : t⁻¹=t := inv_eq_of_mul_eq_one_left (by decide)
  have hu : u⁻¹=u := inv_eq_of_mul_eq_one_left (by decide)
  rw [ht,hu]
  apply orderOf_eq_prime
  · apply Subtype.ext
    ext i
    fin_cases i <;> simp [pow_succ,t,u,Equiv.swap_apply_def]
  · intro he
    have hh := congrArg (fun g:alternatingGroup (Fin 5)=>g.val 0) he
    exact (by decide : (3:Fin 5)≠0) hh

private theorem exists_comm_order_five (a:alternatingGroup (Fin 5))(ha:orderOf a=2) :
    ∃b,orderOf (a*b*a⁻¹*b⁻¹)=5 := by
  obtain ⟨c,hc⟩ := isConj_iff.mp (alternatingGroup.five_involutions_isConj t a t_order ha)
  refine ⟨c*u*c⁻¹,?_⟩
  rw [←hc]
  have he : (c*t*c⁻¹)*(c*u*c⁻¹)*(c*t*c⁻¹)⁻¹*(c*u*c⁻¹)⁻¹ =
      c*(t*u*t⁻¹*u⁻¹)*c⁻¹ := by group
  rw [he, ← SemiconjBy.orderOf_eq c (show SemiconjBy c (t*u*t⁻¹*u⁻¹) (c*(t*u*t⁻¹*u⁻¹)*c⁻¹) from by unfold SemiconjBy; group)]
  exact comm_order

variable {G W:Type*} [Group G] [Finite G] [AddCommGroup W] [Module (ZMod 2) W]
  [FiniteDimensional (ZMod 2) W]

theorem displacement_ge_two_of_alternating_five_quotient
    (ρ:Representation (ZMod 2) G W)(hf:Function.Injective ρ)
    (q:G→*alternatingGroup (Fin 5))(hs:Function.Surjective q)
    (a:G)(ha:orderOf (q a)=2) : 2≤fixedCodim ρ (zpowers a) := by
  obtain ⟨b,hb⟩ := exists_comm_order_five (q a) ha
  obtain ⟨x,rfl⟩ := hs b
  have hlo := prime_order_image_le_fixedCodim ρ hf q (by decide : Nat.Prime 5)
    (by decide) (a*x*a⁻¹*x⁻¹) (by simpa only [map_mul,map_inv] using hb)
  rw [BinaryPrimeDegree.orderOf_two_mod_five] at hlo
  have hhi := fixedCodim_commutator_le_twice ρ a x
  omega
end Representation.BinaryOffender
