module

public import CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.CartanTransport
public import CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.Reduction
public import CFSG.Quasithin.ChapterE.Defs

/-!
# Shared output for the E.6.27 Cartan construction

The definition below specifies the two alternatives to be constructed from
E.2.2 and 4.4.13. It records an actual faithful cyclic Cartan with its full
E.3.37 overgroup, or a nontrivial odd local with an escaping relative
normalizer. It asserts neither their existence nor Proposition E.6.27.

Source: Aschbacher--Smith, combined manuscript (1 March 2004), printed p.257.
-/

@[expose] public section

namespace CFSG.Quasithin.ChapterE.Section06.FixedPointBounds

open Subgroup

variable {G : Type*} [Group G] [Finite G]

/-- The concrete alternatives needed for an escaping large minimal parabolic.
This is an output specification: no existence or source theorem is asserted
by this definition. The second normalizer is the relative normalizer in `H`. -/
def ParabolicCartanAlternative (V M U H : Subgroup G) (n : ℕ) : Prop :=
  (∃ w : NPrimeWitness ↥(M ⊓ centralizer (U : Set G)) n,
    w.cyclicGroup.map (M ⊓ centralizer (U : Set G)).subtype ≤ H ∧
    w.cyclicGroup.map (M ⊓ centralizer (U : Set G)).subtype ⊓
      centralizer (V : Set G) = ⊥) ∨
  ∃ X : Subgroup G, X ≠ ⊥ ∧ X ≤ H ⊓ M ⊓ centralizer (V : Set G) ∧
    Odd (Nat.card X) ∧ ¬ H ⊓ normalizer (X : Set G) ≤ M

end CFSG.Quasithin.ChapterE.Section06.FixedPointBounds

end
