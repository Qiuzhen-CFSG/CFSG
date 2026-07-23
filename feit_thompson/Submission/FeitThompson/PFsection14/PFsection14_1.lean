module

public import Submission.FeitThompson.PFsection14.Basic

/-!
# Peterfalvi, Section 14: Theorem (14.1)
-/

noncomputable section

open scoped BigOperators

attribute [local instance] Fintype.ofFinite

namespace Section14
universe u v w

/-! ## (14.1) -/

/-- Peterfalvi Hypothesis `(14.1)`. -/
@[expose] public def hypothesis_14_1_statement
    (p q : ℕ) : Prop :=
  q < p

end Section14
