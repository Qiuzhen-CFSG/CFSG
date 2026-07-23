module

public import Submission.FeitThompson.PFsection10.Basic
import Submission.FeitThompson.PFsection8.SourceTypePBridge
import Submission.FeitThompson.PFsection5.PFsection5_8
import Submission.FeitThompson.PFsection5.PFsection5_9
import Submission.FeitThompson.PFsection7.PFsection7_5
import Submission.FeitThompson.PFsection7.PFsection7_8_a
import Submission.FeitThompson.PFsection7.PFsection7_8_b
import Submission.FeitThompson.PFsection8.PFsection8_13
import Submission.FeitThompson.PFsection8.PFsection8_15
import Submission.FeitThompson.PFsection8.PFsection8_16
import Submission.FeitThompson.PFsection8.PFsection8_18
import Submission.FeitThompson.PFsection8.PFsection8_9
import Submission.FeitThompson.PFsection2.PFsection2_7_11
import Submission.FeitThompson.PFsection6.PFsection6_5_a
import Submission.FeitThompson.PFsection6.PFsection6_5_b
import Submission.FeitThompson.PFsection6.PFsection6_5_c
import Submission.FeitThompson.PFsection6.PFsection6_8
import Submission.FeitThompson.PFsection9.PFsection9_3
import Submission.FeitThompson.PFsection9.PFsection9_4
import Submission.FeitThompson.PFsection9.PFsection9_6
public import Submission.FeitThompson.PFsection9.PFsection9_11

/-!
# Peterfalvi, Section 10: Theorem (10.8)
-/

noncomputable section

open scoped BigOperators

attribute [local instance] Fintype.ofFinite

namespace Section10
universe u v w

/-! ## (10.8) -/

/-- Peterfalvi `(10.8)`. -/
@[expose] public def theorem_10_8_statement
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (M MF W1 W2 : Subgroup G)
    (V : Set G)
    (S : Finset (Section1.ClassFunction M))
    (τ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G) : Prop :=
  hypothesis_10_1_data M MF W1 W2 V S τ →
    ¬ Section6.coherentFamily S τ

end Section10
