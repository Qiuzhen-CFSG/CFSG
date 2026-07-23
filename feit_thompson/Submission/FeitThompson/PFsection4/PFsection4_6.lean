module

public import Submission.FeitThompson.PFsection4.Basic
public import Submission.FeitThompson.PFsection4.PFsection4_2
public import Submission.FeitThompson.PFsection2.Basic
public import Submission.FeitThompson.PFsection1.PFsection1_2
public import Submission.FeitThompson.PFsection1.PFsection1_5
public import Submission.FeitThompson.PFsection1.PFsection1_6
public import Submission.FeitThompson.HallSubgroups.Core

/-!
# Peterfalvi, Section 4: Theorem (4.6)
-/

noncomputable section

open scoped BigOperators

attribute [local instance] Fintype.ofFinite

namespace Section4Scratch
universe u
universe v

/-! ## (4.6) -/

@[expose] public def hypothesis_4_6_statement
    {L : Type u} [Group L] [Finite L]
    (K W1 W2 W H : Subgroup L)
    (A : Set L) : Prop :=
  Section4.hypothesis_4_2_statement K W1 W2 W ∧
    H.Normal ∧
    W2 ≤ H ∧
    H ≤ K ∧
    (⋃ h : {h : H // (h : L) ≠ 1},
      (((Section2.centralizerIn K ((h : H) : L)) : Set L) \ {1})) ⊆ A ∧
    A ⊆ ((K : Set L) \ {1})

end Section4Scratch
