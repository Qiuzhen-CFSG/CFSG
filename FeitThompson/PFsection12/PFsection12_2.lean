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
# Peterfalvi, Section 12: Theorem (12.2)
-/

noncomputable section

open scoped BigOperators

attribute [local instance] Fintype.ofFinite

namespace Section12
universe u v

/-! ## (12.2) -/

/-- Peterfalvi `(12.2)(a)`. -/
@[expose] public def theorem_12_2_a_statement
    {G : Type u} [Group G] [Finite G]
    (L H : Subgroup G)
    (S : Finset (Section1.ClassFunction L))
    (R : G → Subgroup G)
    (τ : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G)
    : Prop :=
  hypothesis_12_1_data L H S R τ →
    ∃ SX : S → Finset (Section1.ClassFunction L),
      constituentFamilyData L H S SX R τ

/-- Peterfalvi `(12.2)(b)`. -/
@[expose] public def theorem_12_2_b_statement
    {G : Type u} [Group G] [Finite G]
    (L H : Subgroup G)
    (S : Finset (Section1.ClassFunction L))
    (SX : S → Finset (Section1.ClassFunction L))
    (Rade : G → Subgroup G)
    (τ : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G) : Prop :=
  hypothesis_12_1_data L H S Rade τ →
    constituentFamilyData L H S SX Rade τ →
      ∃ R1 : Section1.ClassFunction L → Finset (Section1.ClassFunction G),
      ∃ R : S → Finset (Section1.ClassFunction G),
      (∀ χ : S, rFamilyData (χ : Section1.ClassFunction L) (SX χ) τ R1 (R χ)) ∧
        hypothesis52WithRData S τ R

end Section12
