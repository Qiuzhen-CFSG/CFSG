module

public import FeitThompson.PFsection12.Basic
import FeitThompson.GroupAction.MinimalNormal
import FeitThompson.PFsection5.RealVirtualParity
import FeitThompson.PFsection6.PFsection6_5_a
import FeitThompson.PFsection7.PFsection7_3
import FeitThompson.PFsection7.PFsection7_5
import FeitThompson.PFsection7.PFsection7_7
import FeitThompson.PFsection7.PFsection7_8_a
import FeitThompson.PFsection7.PFsection7_8_b
import FeitThompson.PFsection7.PFsection7_8_c
import FeitThompson.PFsection7.PFsection7_9
import FeitThompson.PFsection8.PFsection8_16
import FeitThompson.PFsection8.SourceTypePBridge
import FeitThompson.PFsection9.PFsection9_1
import Mathlib.GroupTheory.Schreier
import Mathlib.RingTheory.ZMod.UnitsCyclic

/-!
# Peterfalvi, Section 12: Theorem (12.1)
-/

noncomputable section

open scoped BigOperators

attribute [local instance] Fintype.ofFinite

namespace Section12
universe u v

/-! ## (12.1) -/

/-- Peterfalvi Hypothesis `(12.1)`. -/
@[expose] public def hypothesis_12_1_statement
    {G : Type u} [Group G] [Finite G]
    (L H : Subgroup G)
    (S : Finset (Section1.ClassFunction L))
    (R : G → Subgroup G)
    (τ : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G) : Prop :=
  hypothesis_12_1_data L H S R τ

end Section12
