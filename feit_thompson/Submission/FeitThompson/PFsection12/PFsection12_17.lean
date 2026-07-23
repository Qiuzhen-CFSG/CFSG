module

public import Submission.FeitThompson.PFsection12.Basic
import Submission.FeitThompson.PFsection12.PFsection12_7
import Submission.FeitThompson.GroupAction.MinimalNormal
import Submission.FeitThompson.PFsection5.RealVirtualParity
import Submission.FeitThompson.PFsection6.PFsection6_5_a
import Submission.FeitThompson.PFsection7.PFsection7_3
import Submission.FeitThompson.PFsection7.PFsection7_5
import Submission.FeitThompson.PFsection7.PFsection7_7
import Submission.FeitThompson.PFsection7.PFsection7_8_a
import Submission.FeitThompson.PFsection7.PFsection7_8_b
import Submission.FeitThompson.PFsection7.PFsection7_8_c
import Submission.FeitThompson.PFsection7.PFsection7_9
import Submission.FeitThompson.PFsection8.PFsection8_16
import Submission.FeitThompson.PFsection8.SourceTypePBridge
import Submission.FeitThompson.PFsection9.PFsection9_1
import Mathlib.GroupTheory.Schreier
import Mathlib.RingTheory.ZMod.UnitsCyclic

/-!
# Peterfalvi, Section 12: Theorem (12.17)
-/

noncomputable section

open scoped BigOperators

attribute [local instance] Fintype.ofFinite

namespace Section12
universe u v

/-! ## (12.17) -/

/-- Peterfalvi `(12.17)`.

Case (b) of Theorem `(8.8)` holds. -/
public theorem theorem_12_17
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    : ∃ W W1 W2 S T SF TF : Subgroup G,
      Section8.theorem_8_8_source_case_b_data W W1 W2 S T SF TF := by
  exact
    theorem_12_17_source_data_of_all_typeI_contradiction_source_data
      (G := G)
      (Section8.theorem_8_8 (G := G))
      (theorem_12_17_all_typeI_contradiction (G := G))
      (inferInstance : IsMinCE G)


end Section12
