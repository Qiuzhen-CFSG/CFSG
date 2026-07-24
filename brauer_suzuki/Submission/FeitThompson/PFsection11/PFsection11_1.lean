module

public import Submission.FeitThompson.PFsection11.Basic
import Submission.FeitThompson.BGsection6.lemma_6_5_a
import Submission.FeitThompson.BGsection6.lemma_6_3_a_1
import Submission.FeitThompson.PFsection6.PFsection6_2
import Submission.FeitThompson.PFsection6.PFsection6_3
import Submission.FeitThompson.PFsection6.PFsection6_5_b
import Submission.FeitThompson.PFsection2.PFsection2_7_11
import Submission.FeitThompson.PFsection8.PFsection8_5_a
import Submission.FeitThompson.PFsection8.PFsection8_5_b
import Submission.FeitThompson.PFsection8.PFsection8_8
import Submission.FeitThompson.PFsection8.SourceTypePBridge
import Submission.FeitThompson.PFsection4.PFsection4_4
import Submission.FeitThompson.PFsection5.PFsection5_7
import Submission.FeitThompson.PFsection5.PFsection5_8
import Submission.FeitThompson.PFsection5.PFsection5_9
import Submission.FeitThompson.PFsection5.RealVirtualParity
import Submission.FeitThompson.PFsection9.PFsection9_3
import Submission.FeitThompson.PFsection9.PFsection9_4
import Submission.FeitThompson.PFsection9.PFsection9_6
import Submission.FeitThompson.PFsection9.PFsection9_7
import Submission.FeitThompson.PFsection9.PFsection9_8
import Submission.FeitThompson.PFsection9.PFsection9_11
import Submission.FeitThompson.PFsection4.PFsection4_5_to_10

/-!
# Peterfalvi, Section 11: Theorem (11.1)
-/

noncomputable section

open scoped BigOperators

attribute [local instance] Fintype.ofFinite

namespace Section11
universe u v w

/-! ## (11.1) -/

/-- Peterfalvi `(11.1)`. -/
@[expose] public def theorem_11_1_statement
    (p q : ℕ) : Prop :=
  p.Prime → q.Prime → Odd p → Odd q → p ≠ q → p ^ q > 4 * q ^ 2 + 1

end Section11
