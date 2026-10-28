module

public import Theory.Representation.BinaryPrimeDisplacement
public import Theory.SpecificGroups.Alternating.FiveInvolutionFusion
public import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple
import Mathlib.Tactic.FinCases

/-!
# Binary involution displacement in A₅

A double transposition has an order-five commutator with another double
transposition. An order-five actor on a faithful binary module moves at least
four dimensions, whereas the commutator rank is at most twice the original
displacement. Involution conjugacy gives the bound for every involution.
Simplicity then excludes displacement at most one in any nontrivial action.

Source application: Aschbacher–Smith, combined manuscript of 1 March 2004,
proof of 14.7.71(1), printed p.1075. This proves the chief-factor rank bound
without an irreducible-module catalogue.
-/

public section

open Subgroup Representation Representation.BinaryOffender
namespace Representation.AlternatingFiveInvolutionDisplacement
private def t : alternatingGroup (Fin 5) :=
  ⟨Equiv.swap 0 1 * Equiv.swap 2 3, by rw [Equiv.Perm.mem_alternatingGroup]; decide⟩
private def u : alternatingGroup (Fin 5) :=
  ⟨Equiv.swap 1 2 * Equiv.swap 3 4, by rw [Equiv.Perm.mem_alternatingGroup]; decide⟩

private theorem t_order : orderOf t = 2 :=
  orderOf_eq_prime (by decide) (by decide)

private theorem commutator_order : orderOf (t * u * t⁻¹ * u⁻¹) = 5 := by
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  have ht : t⁻¹ = t := inv_eq_of_mul_eq_one_left (by decide)
  have hu : u⁻¹ = u := inv_eq_of_mul_eq_one_left (by decide)
  rw [ht, hu]
  apply orderOf_eq_prime
  · apply Subtype.ext
    ext i
    fin_cases i <;> simp [pow_succ, t, u, Equiv.swap_apply_def]
  · intro he
    have h := congrArg (fun g : alternatingGroup (Fin 5) => g.val 0) he
    exact (by decide : (3 : Fin 5) ≠ 0) h

variable {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
  [FiniteDimensional (ZMod 2) W]

/-- Every involution in a faithful binary A₅ action moves at least two dimensions. -/
theorem displacement_lower (ρ : Representation (ZMod 2) (alternatingGroup (Fin 5)) W)
    (hρ : Function.Injective ρ) (a : alternatingGroup (Fin 5)) (ha : orderOf a = 2) :
    2 ≤ Module.finrank (ZMod 2) (ρ a - LinearMap.id).range := by
  have hlo := prime_order_le_fixedCodim ρ hρ (by decide : Nat.Prime 5)
    (by decide) (t * u * t⁻¹ * u⁻¹) commutator_order
  rw [BinaryPrimeDegree.orderOf_two_mod_five] at hlo
  have hhi := fixedCodim_commutator_le_twice ρ t u
  have ht : 2 ≤ fixedCodim ρ (zpowers t) := by omega
  obtain ⟨c, hc⟩ := (isConj_iff.mp (alternatingGroup.five_involutions_isConj t a t_order ha))
  rw [← fixedCodim_zpowers_eq_displacement_rank, ← hc, fixedCodim_zpowers_conj]
  exact ht

/-- One involution of displacement at most one forces the entire A₅ action to be trivial. -/
theorem trivial_of_displacement_le_one
    (ρ : Representation (ZMod 2) (alternatingGroup (Fin 5)) W)
    (a : alternatingGroup (Fin 5)) (ha : orderOf a = 2)
    (hr : Module.finrank (ZMod 2) (ρ a - LinearMap.id).range ≤ 1) :
    ∀ g, ρ g = 1 := by
  rcases (MonoidHom.normal_ker ρ).eq_bot_or_eq_top with hk | hk
  · have h := displacement_lower ρ (ρ.ker_eq_bot_iff.mp hk) a ha
    omega
  · intro g
    exact show g ∈ ρ.ker from hk ▸ mem_top g

end Representation.AlternatingFiveInvolutionDisplacement
