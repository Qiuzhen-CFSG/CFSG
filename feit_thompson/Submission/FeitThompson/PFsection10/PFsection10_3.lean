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
# Peterfalvi, Section 10: Theorem (10.3)
-/

noncomputable section

open scoped BigOperators

attribute [local instance] Fintype.ofFinite

namespace Section10
universe u v w

/-! ## (10.3) -/

/-- Peterfalvi `(10.3)`. -/
@[expose] public def theorem_10_3_statement
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    (M MF W1 W2 : Subgroup G)
    (V : Set G)
    (W : Subgroup M)
    (A A0 : Set M)
    (S : Finset (Section1.ClassFunction M))
    (τ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G)
    (i0 : I)
    (j0 : J)
    (μ : I → J → Section1.ClassFunction M)
    (δSign : J → ℤ)
    (ω : I → J → Section1.ClassFunction W)
    (σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G)
    : Prop :=
  hypothesis_10_1_data M MF W1 W2 V S τ →
    section10FourSixNotationData M W1 W2 W A A0 i0 j0 μ δSign ω σ τ →
      ∃ d n : ℕ, ∃ δ : ℤ,
        uniformMuData W1 W2 j0 μ δSign d n δ

end Section10
