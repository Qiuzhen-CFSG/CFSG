module
public import Theory.Representation.PSL3Two.ParabolicCyclic.ChiefCounts.DualCore.Extension
public import Theory.Representation.PSL3Two.ParabolicCyclic.ChiefCounts.Refinement
/-!
# Lifting the noncentral chief count through a fixed kernel

A fixed kernel contributes only central chief factors. The first
isomorphism theorem identifies the remaining quotient action, and
concatenating actual chief flags preserves the noncentral count.

Source application: Aschbacher–Smith, 13.7.6(3a), printed p.939.
-/
@[expose] public section
open Representation
namespace BinaryLinearThree.ParabolicCyclic.ChiefCounts
variable {G E F : Type*} [Group G]
  [AddCommGroup E] [Module (ZMod 2) E] [Finite E]
  [AddCommGroup F] [Module (ZMod 2) F]
  {ρ : Representation (ZMod 2) G E} {σ : Representation (ZMod 2) G F}
/-- A surjective equivariant map with pointwise fixed kernel loses no
noncentral chief factors when lifting a complete quotient chief flag. -/
theorem HasCount.of_surjective_fixed_kernel {n : ℕ}
    (p : ρ.IntertwiningMap σ) (hp : Function.Surjective p)
    (hk : ∀ g x, p x = 0 → ρ g x = x) (hc : HasCount σ n) : HasCount ρ n := by
  have hker : HasCount p.ker.toRepresentation 0 := by
    apply exists_central_series ⊥ ⊤ bot_le
    intro g x _
    change p.ker.toRepresentation g x - x = 0
    apply sub_eq_zero.mpr
    exact Subtype.ext (hk g x x.property)
  let e : (E ⧸ p.ker.toSubmodule) ≃ₗ[ZMod 2] F :=
    p.toLinearMap.quotKerEquivOfSurjective hp
  let er : p.ker.quotientRepresentation.Equiv σ := .mk e (by
    intro g
    apply LinearMap.ext
    intro v
    induction v using Submodule.Quotient.induction_on with
    | _ u =>
      change p (ρ g u) = σ g (p u)
      exact IntertwiningMap.isIntertwining _ _ p g u)
  have hquot := hc.mapEquiv er.symm
  simpa only [zero_add] using HasCount.of_subrepresentation p.ker hker hquot
end BinaryLinearThree.ParabolicCyclic.ChiefCounts
