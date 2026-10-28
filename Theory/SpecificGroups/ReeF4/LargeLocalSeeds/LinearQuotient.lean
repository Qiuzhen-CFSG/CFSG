module

public import Theory.SpecificGroups.ReeF4.Field
public import Mathlib.LinearAlgebra.Projectivization.PSL.PSL2

/-!
# Simplicity of the large Ree linear local quotient

For m ≥ 1 the Ree coefficient field has at least eight elements. Mathlib's
projective-line proof of simplicity therefore applies to PSL₂ over this
exact field. This certifies the target of a local quotient isomorphism;
it neither constructs that isomorphism nor certifies simplicity of ²F₄.

Source: the L₂(q) quotient in Aschbacher–Smith F.1.12(I)(5), printed p.263.
-/

@[expose] public section

namespace ReeF4.LargeLocalSeeds

/-- The actual projective matrix quotient over the Ree coefficient field. -/
noncomputable abbrev LinearQuotient (m : ℕ) :=
  Matrix.ProjectiveSpecialLinearGroup (Fin 2) (ReeF4.CoefficientField m)

theorem linearQuotient_simple (m : ℕ) (hm : 1 ≤ m) :
    IsSimpleGroup (LinearQuotient m) := by
  apply Matrix.ProjectiveSpecialLinearGroup.rank_two_simple
  rw [ReeF4.field_card]
  have h := pow_le_pow_right₀ (by decide : 1 ≤ 2) (by omega : 2 ≤ 2 * m + 1)
  exact h

end ReeF4.LargeLocalSeeds

end
