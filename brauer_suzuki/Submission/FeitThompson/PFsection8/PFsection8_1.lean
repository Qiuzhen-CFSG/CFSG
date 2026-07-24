module

public import Submission.FeitThompson.PFsection8.Basic

/-!
# Peterfalvi, Section 8: Theorem (8.1)
-/

noncomputable section

open scoped BigOperators

attribute [local instance] Fintype.ofFinite

namespace Section8
universe u
universe v
universe w

@[expose] public def definition_8_1_statement
    {G : Type u} [Group G] [Finite G]
    (M MF U U1 U0 : Subgroup G) : Prop :=
  typeFData M MF U U1 U0

end Section8
