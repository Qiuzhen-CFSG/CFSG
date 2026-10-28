module

public import Mathlib.GroupTheory.Perm.List
public import Mathlib.GroupTheory.Subgroup.Centralizer
public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.Data.Fintype.Perm

/-!
# The concrete five-point quotient model

The normalizer of the displayed five-cycle is the Frobenius group acting
on five points. It provides a common concrete quotient for two independent
calculations: the marked M₂₂ centralizer modulo its elementary kernel, and
the degenerate Suzuki matrix group. An isomorphism of these models, rather
than agreement of their orders, is required in the final extension.

Source: the `Sz(2)/E₁₆` alternative in Aschbacher–Smith 16.1.5(5), p.1171.
-/

@[expose] public section
namespace Sporadic.Mathieu.M22OuterCentralizers.FixedPointFree

/-- The displayed regular five-cycle. -/
def fiveCycle : Equiv.Perm (Fin 5) := List.formPerm [0,1,2,3,4]

/-- The full permutation normalizer of the marked cyclic group of order five. -/
def fiveNormalizer : Subgroup (Equiv.Perm (Fin 5)) :=
  Subgroup.normalizer (Subgroup.zpowers fiveCycle : Set (Equiv.Perm (Fin 5)))

theorem fiveCycle_order : orderOf fiveCycle = 5 := by
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  apply orderOf_eq_prime
  · decide +kernel
  · decide +kernel

end Sporadic.Mathieu.M22OuterCentralizers.FixedPointFree
