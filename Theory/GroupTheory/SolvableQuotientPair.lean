module
public import Mathlib.GroupTheory.Solvable
public import Mathlib.GroupTheory.Index

/-!
# Two quotient actions with a solvable common kernel

This structural condition records two normal kernels with solvable
intersection and quotient orders avoiding a specified divisor. The
quotients may separately have nonsolvable images; the condition does
not assert solvability of the whole group.

It is used with invariant sections of a Sylow subgroup in the
Aschbacher--Smith 4.4.10--11 source argument.
-/

namespace Theory.GroupTheory
/-- Two quotient actions detect the group modulo a solvable common kernel,
and neither quotient order is divisible by n. -/
@[expose] public def HasSolvableQuotientPair (n : ℕ) (G : Type*) [Group G] : Prop :=
  ∃ A C : Subgroup G, A.Normal ∧ C.Normal ∧
    Group.IsSolvable (A ⊓ C : Subgroup G) ∧ ¬ n ∣ A.index ∧ ¬ n ∣ C.index
end Theory.GroupTheory
