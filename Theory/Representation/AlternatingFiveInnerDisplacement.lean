module
public import Theory.Representation.AlternatingFiveInvolutionDisplacement
import Mathlib.Tactic.FinCases

/-!
# Small binary actors inducing inner automorphisms of A₅

A nonidentity inner involution has an order-five commutator with a suitable
A₅ element. In a faithful binary action that commutator moves at least four
dimensions, while an actor of displacement at most one gives a commutator
of displacement at most two. Thus the inner involution must be trivial.
The argument allows arbitrary fixed summands and needs no irreducibility.

Source: Aschbacher--Smith, 14.3.25, printed p.1001, the faithful-component
transvection contradiction. The two double transpositions and quintic
calculation follow AlternatingFiveInvolutionDisplacement.lean.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender
namespace Representation.AlternatingFiveInvolutionDisplacement
private def t₀ : alternatingGroup (Fin 5) :=
  ⟨Equiv.swap 0 1 * Equiv.swap 2 3, by rw [Equiv.Perm.mem_alternatingGroup]; decide⟩
private def u₀ : alternatingGroup (Fin 5) :=
  ⟨Equiv.swap 1 2 * Equiv.swap 3 4, by rw [Equiv.Perm.mem_alternatingGroup]; decide⟩

private theorem t₀_order : orderOf t₀ = 2 := orderOf_eq_prime (by decide) (by decide)
private theorem commutator₀_order : orderOf (t₀ * u₀ * t₀⁻¹ * u₀⁻¹) = 5 := by
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  have ht : t₀⁻¹ = t₀ := inv_eq_of_mul_eq_one_left (by decide)
  have hu : u₀⁻¹ = u₀ := inv_eq_of_mul_eq_one_left (by decide)
  rw [ht, hu]
  apply orderOf_eq_prime
  · apply Subtype.ext
    ext i
    fin_cases i <;> simp [pow_succ, t₀, u₀, Equiv.swap_apply_def]
  · intro he
    have h := congrArg (fun g : alternatingGroup (Fin 5) => g.val 0) he
    exact (by decide : (3 : Fin 5) ≠ 0) h

private theorem exists_quintic_commutator (a : alternatingGroup (Fin 5)) (ha : orderOf a = 2) :
    ∃ b, orderOf (a*b*a⁻¹*b⁻¹) = 5 := by
  obtain ⟨c,hc⟩ := isConj_iff.mp (alternatingGroup.five_involutions_isConj t₀ a t₀_order ha)
  refine ⟨c*u₀*c⁻¹, ?_⟩
  have he : a*(c*u₀*c⁻¹)*a⁻¹*(c*u₀*c⁻¹)⁻¹ =
      c*(t₀*u₀*t₀⁻¹*u₀⁻¹)*c⁻¹ := by rw [←hc]; group
  rw [he, ← MulAut.conj_apply, (MulAut.conj c).orderOf_eq]
  exact commutator₀_order

variable {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
  [FiniteDimensional (ZMod 2) W]

/-- A rank-at-most-one actor cannot induce a nonidentity inner involution on A₅. -/
theorem inner_involution_eq_one_of_rank_le_one
    (ρ : Representation (ZMod 2) (alternatingGroup (Fin 5)) W)
    (hρ : Function.Injective ρ) (t : (Module.End (ZMod 2) W)ˣ)
    (s : alternatingGroup (Fin 5)) (hs : s ^ 2 = 1)
    (hinner : ∀ b, t * ρ.asGroupHom b * t⁻¹ = ρ.asGroupHom (s*b*s⁻¹))
    (hr : Module.finrank (ZMod 2) ((t : Module.End (ZMod 2) W) - LinearMap.id).range ≤ 1) : s = 1 := by
  by_contra hs1
  obtain ⟨b,hb⟩ := exists_quintic_commutator s (orderOf_eq_prime hs hs1)
  have hl := prime_order_le_fixedCodim ρ hρ (by decide : Nat.Prime 5)
    (by decide) (s*b*s⁻¹*b⁻¹) hb
  rw [BinaryPrimeDegree.orderOf_two_mod_five, fixedCodim_zpowers_eq_displacement_rank] at hl
  have hu := fixedCodim_commutator_le_twice
    (Units.coeHom (Module.End (ZMod 2) W)) t (ρ.asGroupHom b)
  rw [fixedCodim_zpowers_eq_displacement_rank, fixedCodim_zpowers_eq_displacement_rank] at hu
  have he : t * ρ.asGroupHom b * t⁻¹ * (ρ.asGroupHom b)⁻¹ =
      ρ.asGroupHom (s*b*s⁻¹*b⁻¹) := by
    rw [hinner, ← map_inv, ← map_mul]
  rw [he] at hu
  change Module.finrank (ZMod 2) (ρ (s*b*s⁻¹*b⁻¹) - LinearMap.id).range ≤
    2 * Module.finrank (ZMod 2) ((t : Module.End (ZMod 2) W) - LinearMap.id).range at hu
  omega
end Representation.AlternatingFiveInvolutionDisplacement
