module
public import Theory.Representation.BinaryOffender.NaturalTensorFixedCodimension.Basic
public import Theory.Representation.ScalarDescent

/-!
# Scalar extension of a binary actor's quadratic displacement budget

A field extension preserves the rank of each displacement operator: flat base
change identifies its kernel, and rank-nullity gives the rank equality.
The quadratic identity is a zero product of two displacement operators, so it
also survives base change. Together these facts transfer the original binary
fixed-codimension budget to every element of the same actor over an extension
field.

The source application is the full Suzuki Steinberg actor in Aschbacher–Smith
§13.6, printed pp.934–935. No faithfulness or quotient of the actor is needed.
-/

public noncomputable section
open scoped TensorProduct
namespace Representation.BinaryOffender
open NaturalTensor

/-- Displacement rank is unchanged when the coefficient field is extended. -/
theorem operatorFixedCodim_extendScalars {E F G W : Type*}
    [Field E] [Field F] [Algebra E F] [Group G]
    [AddCommGroup W] [Module E W] [FiniteDimensional E W]
    (ρ : Representation E G W) (g : G) :
    operatorFixedCodim (extendScalars F ρ g) = operatorFixedCodim (ρ g) := by
  have hk := (LinearMap.kerBaseChangeEquiv (E := F) (ρ g - 1)).finrank_eq
  rw [Module.finrank_baseChange, LinearMap.baseChange_sub, LinearMap.baseChange_one] at hk
  have hF := operatorFixedCodim_add_finrank (extendScalars F ρ g)
  have hE := operatorFixedCodim_add_finrank (ρ g)
  rw [Module.finrank_baseChange] at hF
  change Module.finrank E (ρ g - 1).ker =
    Module.finrank F (extendScalars F ρ g - 1).ker at hk
  omega

/-- The quadratic displacement identity survives extension of scalars. -/
theorem IsQuadratic.extendScalars {G W F : Type*}
    [Group G] [AddCommGroup W] [Module (ZMod 2) W]
    [Field F] [Algebra (ZMod 2) F]
    {ρ : Representation (ZMod 2) G W} {B : Subgroup G}
    (hquad : IsQuadratic ρ B) :
    ∀ (a b : B) v, extendScalars F ρ a (extendScalars F ρ b v - v) =
      extendScalars F ρ b v - v := by
  intro a b v
  have hz : (ρ a - 1) * (ρ b - 1) = 0 := by
    ext w
    simpa only [Module.End.mul_apply, LinearMap.sub_apply, Module.End.one_apply,
      LinearMap.zero_apply, sub_eq_zero] using hquad a a.property b b.property w
  have hz' := congrArg (LinearMap.baseChange F) hz
  simp only [LinearMap.baseChange_mul, LinearMap.baseChange_sub,
    LinearMap.baseChange_one, LinearMap.baseChange_zero] at hz'
  have hv := congrArg (fun T : Module.End F (F ⊗[ZMod 2] W) => T v) hz'
  simpa only [Module.End.mul_apply, LinearMap.sub_apply, Module.End.one_apply,
    LinearMap.zero_apply, sub_eq_zero, extendScalars_apply] using hv

/-- The same binary actor's ratio budget bounds every scalar-extended operator. -/
theorem extendScalars_operatorFixedCodim_le_of_fixedCodim
    {G W F : Type*} [Group G] [AddCommGroup W] [Module (ZMod 2) W]
    [FiniteDimensional (ZMod 2) W] [Field F] [Algebra (ZMod 2) F]
    (ρ : Representation (ZMod 2) G W) (B : Subgroup G)
    (hsmall : fixedCodim ρ B ≤ 2 * rank B) (b : B) :
    operatorFixedCodim (extendScalars F ρ b) ≤ 2 * Nat.log 2 (Nat.card B) := by
  rw [operatorFixedCodim_extendScalars]
  exact (operatorFixedCodim_le_fixedCodim ρ B b.property).trans hsmall

end Representation.BinaryOffender
