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
# Peterfalvi, Section 10: Theorem (10.10)
-/

noncomputable section

open scoped BigOperators

attribute [local instance] Fintype.ofFinite

namespace Section10
universe u v w

/-! ## (10.10) -/

/-- Peterfalvi `(10.10)`: `G` has no maximal subgroup of Type V. -/
@[expose] public def theorem_10_10_statement
    {G : Type u} [Group G] [Finite G] [IsMinCE G] : Prop :=
  ¬ ∃ M MF : Subgroup G,
    M ∈ section9MaximalSubgroups G ∧
      section16MFSubgroup M MF ∧
      Section8.typeVDefinitionData M MF

/-- Peterfalvi `(10.10.1)`. -/
@[expose] public def theorem_10_10_1_statement
    {G : Type u} [Group G] [Finite G]
    (M MF H H' W1 W2 : Subgroup G)
    (p : ℕ) : Prop :=
  typeVReductionData M MF H H' W1 W2 p →
    p = 2 * Nat.card W1 - 1 ∧
      Nat.card W1 < Nat.card W2

/-- Peterfalvi `(10.10.2)`. -/
@[expose] public def theorem_10_10_2_statement
    {G : Type u} [Group G] [Finite G]
    (M MF H H' W1 W2 : Subgroup G)
    (S : Finset (Section1.ClassFunction M))
    (τ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G)
    (p : ℕ) : Prop :=
  typeVReductionData M MF H H' W1 W2 p →
    hypothesis_10_1_data M MF W1 W2 (section16HatW W1 W2) S τ →
      ∃ S₁ : Finset (Section1.ClassFunction M),
      ∃ J : Type u, ∃ instJ : Fintype J,
        ∃ j0 : J,
        ∃ μ : J → Section1.ClassFunction M,
        ∃ d n : ℕ, ∃ δ : ℤ,
          @typeVCharacterCountData G _ _ J instJ M S S₁ W1 j0 μ p d n δ

/-- Peterfalvi `(10.10.3)`. -/
@[expose] public def theorem_10_10_3_statement
    {G : Type u} [Group G] [Finite G]
    {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    (M MF H H' W1 W2 : Subgroup G)
    (W : Subgroup M)
    (A A0 : Set M)
    (S S₁ : Finset (Section1.ClassFunction M))
    (ζ : Section1.ClassFunction M)
    (τ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G)
    (i0 : I)
    (j0 : J)
    (μ : I → J → Section1.ClassFunction M)
    (μcol : J → Section1.ClassFunction M)
    (δSign : J → ℤ)
    (ω : I → J → Section1.ClassFunction W)
    (σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G)
    (p d n : ℕ) (δ : ℤ) : Prop :=
  typeVReductionData M MF H H' W1 W2 p →
    hypothesis_10_1_data M MF W1 W2 (section16HatW W1 W2) S τ →
      typeVCharacterCountData M S S₁ W1 j0 μcol p d n δ →
        section10FourSixNotationData M W1 W2 W A A0 i0 j0 μ δSign ω σ τ →
          (∀ j, μcol j = muColumn μ j) →
            ζ ∈ S₁ →
              ∃ τ₁ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G,
                typeVCoherentSubfamilyData M S₁ τ τ₁ ∧
                  typeVAlphaFormulaData W A0 j0 μ ω σ ζ τ τ₁ n δ

/-- Peterfalvi `(10.10.4)`. -/
@[expose] public def theorem_10_10_4_statement
    {G : Type u} [Group G] [Finite G]
    (M MF H H' W1 W2 : Subgroup G)
    (S : Finset (Section1.ClassFunction M))
    (τ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G)
    (p : ℕ)
    : Prop :=
  hypothesis_10_1_data M MF W1 W2 (section16HatW W1 W2) S τ →
    typeVReductionData M MF H H' W1 W2 p →
      Section6.coherentFamily S τ

end Section10
