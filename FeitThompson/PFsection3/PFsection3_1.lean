module

public import FeitThompson.PFsection3.Basic
public import FeitThompson.PFsection1.PFsection1_9

/-!
# Peterfalvi, Section 3: Theorem (3.1)
-/

noncomputable section

open scoped BigOperators

attribute [local instance] Fintype.ofFinite

namespace Section3
universe u
universe v

/-! ## (3.1) -/

/-- Peterfalvi Hypothesis (3.1). -/
@[expose] public def hypothesis_3_1_statement {G : Type u} [Group G] [Finite G]
    (W1 W2 W : Subgroup G) : Prop :=
  isCyclicTIHypothesis W1 W2 W

end Section3
