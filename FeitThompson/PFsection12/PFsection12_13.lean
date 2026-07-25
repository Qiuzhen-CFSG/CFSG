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
# Peterfalvi, Section 12: Theorem (12.13)
-/

noncomputable section

open scoped BigOperators

attribute [local instance] Fintype.ofFinite

namespace Section12
universe u v

/-! ## (12.13) -/

/-- Peterfalvi Notation `(12.13)`. -/
@[expose] public def notation_12_13_statement
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (L H E : Subgroup G)
    (e : ℕ)
    (S : Finset (Section1.ClassFunction L))
    (R : G → Subgroup G)
    (τ τ₁ : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G)
    (χ : Section1.ClassFunction L)
    (ψ : Section1.ClassFunction G)
    (ψρ : Section1.ClassFunction L) : Prop :=
  notation_12_13_data L H E e S R τ τ₁ χ ψ ψρ

end Section12
