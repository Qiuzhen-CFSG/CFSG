module

public import FeitThompson.PFsection14.Basic

/-!
# Peterfalvi, Section 14: Theorem (14.13)
-/

noncomputable section

open scoped BigOperators

attribute [local instance] Fintype.ofFinite

namespace Section14
universe u v w

/-! ## (14.13) -/

/-- Peterfalvi Hypothesis `(14.13)`. -/
@[expose] public def hypothesis_14_13_statement
    {G : Type u} [Group G] [Finite G]
    (L M H : Subgroup G)
    (h : ℕ) : Prop :=
  (¬ ∃ g : G, L.conjBy g = M) ∧
    h = Nat.card H

end Section14
