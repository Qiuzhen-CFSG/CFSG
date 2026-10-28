module

public import Theory.Representation.QuadraticDuality
public import Theory.Representation.BinaryOffender.FaithfulRankOne

/-!
# The displacement bound for a representation and its dual

The displacement of an actor is a linear map from the fixed-space quotient
to the commutator space. Faithfulness makes these maps distinct. Counting
them, and identifying the commutator dimension by duality, bounds the actor
rank by the product of the two fixed codimensions.

This extracts the general argument in Chapter C's
`ExtensionControl/DualExclusion.lean`. Its consumer is the two-natural-factor
offender budget in Aschbacher–Smith B.4.9, printed pp.94–95, combined
manuscript of 1 March 2004. No quadraticity assumption is needed.
-/

public section
namespace Representation.BinaryOffender
variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V] (ρ : Representation (ZMod 2) G V)

omit [FiniteDimensional (ZMod 2) V] in
/-- Faithfulness passes to the contragredient action. -/
theorem faithful_dual (hρ : Function.Injective ρ) : Function.Injective ρ.dual := by
  intro g h he
  apply inv_injective
  apply hρ
  apply LinearMap.ext
  intro v
  apply Module.eval_apply_injective (ZMod 2)
  ext f
  exact congrArg (fun l : Module.Dual (ZMod 2) V => l v) (LinearMap.congr_fun he f)

/-- Counting displacement maps bounds actor rank by the product of the
fixed codimensions on the original representation and its dual. -/
theorem rank_le_fixedCodim_mul_dual [Finite G] (hρ : Function.Injective ρ)
    (A : Subgroup G) : rank A ≤ fixedCodim ρ A * fixedCodim ρ.dual A := by
  let τ := ρ.comp A.subtype
  let U := fixedSpace ρ A
  let C := Coinvariants.ker τ
  let d (a : A) : V →ₗ[ZMod 2] C :=
    (ρ a - LinearMap.id).codRestrict C (fun v => Coinvariants.sub_mem_ker (ρ := τ) a v)
  let D (a : A) : (V ⧸ U) →ₗ[ZMod 2] C := U.liftQ (d a) (by
    intro v hv
    apply Subtype.ext
    exact sub_eq_zero.mpr (hv a))
  have hinj : Function.Injective D := by
    intro a b h
    apply Subtype.ext
    apply hρ
    apply LinearMap.ext
    intro v
    have he := congrArg (fun f : (V ⧸ U) →ₗ[ZMod 2] C => (f (U.mkQ v) : V)) h
    change ρ a v - v = ρ b v - v at he
    exact sub_left_injective he
  let : Finite ((V ⧸ U) →ₗ[ZMod 2] C) := Module.finite_of_finite (ZMod 2)
  have hc := Nat.card_le_card_of_injective D hinj
  rw [Module.natCard_eq_pow_finrank (K := ZMod 2) (V := (V ⧸ U) →ₗ[ZMod 2] C),
    Nat.card_zmod, Module.finrank_linearMap] at hc
  have hd : fixedCodim ρ.dual A = Module.finrank (ZMod 2) C :=
    finrank_dual_quotient_invariants τ
  have hl := Nat.log_monotone (b := 2) hc
  rw [Nat.log_pow (by decide : 1 < 2)] at hl
  rw [hd]
  exact hl
end Representation.BinaryOffender
