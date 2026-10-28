module

public import Mathlib.GroupTheory.PGroup
public import Mathlib.GroupTheory.SpecificGroups.Alternating
public import Mathlib.GroupTheory.QuotientGroup.Basic

/-!+# Two-group extensions of products of alternating groups

The normal subgroup N has two-power index, and admits a surjection to a finite
direct power of A_d with two-group kernel. Thus both the upper quotient and
the lower kernel are actual two-groups. The definition retains the maps and
normality needed to study subnormal subgroups; an abstract list of composition
factor names would not suffice.

This shape occurs when a two-group permutes the heptad subgroups in an orbit
of M23 components, in Aschbacher–Smith 2.3.9(7)(f), printed pp.525–526.
-/

@[expose] public section

namespace Theory.GroupTheory

/-- A normal subgroup with two-group quotient and a genuine alternating-power
quotient with two-group kernel. A power of exponent zero is allowed. -/
def AlternatingPowerTwoExtension (K : Type*) [Group K] (d : ℕ) : Prop :=
  ∃ N : Subgroup K, ∃ _ : N.Normal,
    IsPGroup 2 (K ⧸ N) ∧
      ∃ n : ℕ, ∃ f : N →* (Fin n → alternatingGroup (Fin d)),
        Function.Surjective f ∧ IsPGroup 2 f.ker

end Theory.GroupTheory

end
