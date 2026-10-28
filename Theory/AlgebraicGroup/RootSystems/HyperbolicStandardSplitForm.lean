module

public import Theory.AlgebraicGroup.RootSystems.CliffordSplitPBW

/-!
# The standard hyperbolic split form

The standard hyperbolic quadratic form on two copies of `Fin n -> k` is
nondegenerate over every field.  The theorem `hyperbolicForm_nondegenerate`
exports this fact, and `standardHyperbolicSplit` packages the form with the
identity isometry as a `SplitQuadraticForm`.  This supplies the reusable split
quadratic-space input, together with an explicit theorem that its recorded
rank is `n`, needed by the concrete even-orthogonal constructions without
importing their type-D classification layer.

For nondegeneracy, a vector in the kernel of the polar map is tested first
against a basis vector in the second coordinate summand and then against one
in the first.  The two tests recover the two coordinates separately, so the
polar map is injective in characteristic two as well as in other
characteristics.  Mathlib's quadratic-radical criterion then gives the result.
The form and splitness interface are those introduced in
`Theory.AlgebraicGroup.RootSystems.CliffordSplitPBW`.
-/

universe u

open scoped BigOperators

namespace Theory.AlgebraicGroup

variable {k : Type u} [Field k]

private theorem hyperbolicPolar_injective (n : Nat) :
    Function.Injective (hyperbolicForm (k := k) n).polarBilin := by
  apply (injective_iff_map_eq_zero _).mpr
  intro v hv
  apply Prod.ext <;> funext i
  · have hi := congrArg (fun f => f (0, Pi.single i 1)) hv
    rw [hyperbolicForm_polar] at hi
    simpa [Pi.single_apply] using hi
  · have hi := congrArg (fun f => f (Pi.single i 1, 0)) hv
    rw [hyperbolicForm_polar] at hi
    simpa [Pi.single_apply] using hi

/-- The standard hyperbolic quadratic form is nondegenerate over every field. -/
public theorem hyperbolicForm_nondegenerate (n : Nat) :
    (hyperbolicForm (k := k) n).Nondegenerate := by
  have hker : (hyperbolicForm (k := k) n).polarBilin.ker = ⊥ :=
    LinearMap.ker_eq_bot.mpr (hyperbolicPolar_injective n)
  constructor
  · apply le_antisymm
    · rw [← hker]
      exact QuadraticMap.radical_le_ker_polarBilin
    · exact bot_le
  · rw [hker]
    simp

/-- The standard hyperbolic form, packaged with its identity split isometry. -/
public noncomputable def standardHyperbolicSplit (n : Nat) :
    SplitQuadraticForm (hyperbolicForm (k := k) n) where
  rank := n
  isometry := QuadraticMap.IsometryEquiv.refl _
  nondegenerate := hyperbolicForm_nondegenerate n

private theorem standardHyperbolicSplit_rank_internal (n : Nat) :
    (standardHyperbolicSplit (k := k) n).rank = n := rfl

@[simp]
public theorem standardHyperbolicSplit_rank (n : Nat) :
    (standardHyperbolicSplit (k := k) n).rank = n :=
  standardHyperbolicSplit_rank_internal n

end Theory.AlgebraicGroup
