module

public import Submission.FeitThompson.PFsection12.Basic
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
# Peterfalvi, Section 12: Theorem (12.3)
-/

noncomputable section

open scoped BigOperators

attribute [local instance] Fintype.ofFinite

namespace Section12
universe u v

/-! ## (12.3) -/

/-- Peterfalvi `(12.3)`. -/
@[expose] public def theorem_12_3_statement
    {G : Type u} [Group G] [Finite G]
    (L1 H1 L2 H2 : Subgroup G)
    (S1 : Finset (Section1.ClassFunction L1))
    (S2 : Finset (Section1.ClassFunction L2))
    (τ1 : Section1.ClassFunction L1 →ₗ[ℂ] Section1.ClassFunction G)
    (τ2 : Section1.ClassFunction L2 →ₗ[ℂ] Section1.ClassFunction G)
    (Rade1 Rade2 : G → Subgroup G)
    (SX1 : S1 → Finset (Section1.ClassFunction L1))
    (SX2 : S2 → Finset (Section1.ClassFunction L2))
    (R1a : Section1.ClassFunction L1 → Finset (Section1.ClassFunction G))
    (R1b : Section1.ClassFunction L2 → Finset (Section1.ClassFunction G))
    (Rfun1 : S1 → Finset (Section1.ClassFunction G))
    (Rfun2 : S2 → Finset (Section1.ClassFunction G))
    (χ1 : Section1.ClassFunction L1)
    (χ2 : Section1.ClassFunction L2)
    (D1 tildeA1 tildeA01 tildeA11 : Set G)
    (D2 tildeA2 tildeA02 tildeA12 : Set G) : Prop :=
  theorem_12_3_source_pair_data L1 H1 L2 H2 S1 S2 τ1 τ2
      Rade1 Rade2 χ1 χ2
      D1 tildeA1 tildeA01 tildeA11 D2 tildeA2 tildeA02 tildeA12 →
    hypothesis_12_1_data L1 H1 S1 Rade1 τ1 →
    hypothesis_12_1_data L2 H2 S2 Rade2 τ2 →
      constituentFamilyData L1 H1 S1 SX1 Rade1 τ1 →
      constituentFamilyData L2 H2 S2 SX2 Rade2 τ2 →
      ¬ section16ConjugateSubgroupsIn (⊤ : Subgroup G) L1 L2 →
        (∀ χ : S1,
          rFamilyData (χ : Section1.ClassFunction L1) (SX1 χ) τ1 R1a
            (Rfun1 χ)) →
          hypothesis52WithRData S1 τ1 Rfun1 →
            (∀ χ : S2,
              rFamilyData (χ : Section1.ClassFunction L2) (SX2 χ) τ2 R1b
                (Rfun2 χ)) →
              hypothesis52WithRData S2 τ2 Rfun2 →
                ∀ (hχ1 : χ1 ∈ S1) (hχ2 : χ2 ∈ S2),
                  Section5.orthogonalFinsets
                    (Rfun1 ⟨χ1, hχ1⟩) (Rfun2 ⟨χ2, hχ2⟩)

end Section12
