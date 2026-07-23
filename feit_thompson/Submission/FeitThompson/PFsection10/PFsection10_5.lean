module

public import FeitThompson.PFsection10.Basic
import FeitThompson.PFsection8.SourceTypePBridge
import FeitThompson.PFsection5.PFsection5_8
import FeitThompson.PFsection5.PFsection5_9
import FeitThompson.PFsection7.PFsection7_5
import FeitThompson.PFsection7.PFsection7_8_a
import FeitThompson.PFsection7.PFsection7_8_b
import FeitThompson.PFsection8.PFsection8_13
import FeitThompson.PFsection8.PFsection8_15
import FeitThompson.PFsection8.PFsection8_16
import FeitThompson.PFsection8.PFsection8_18
import FeitThompson.PFsection8.PFsection8_9
import FeitThompson.PFsection2.PFsection2_7_11
import FeitThompson.PFsection6.PFsection6_5_a
import FeitThompson.PFsection6.PFsection6_5_b
import FeitThompson.PFsection6.PFsection6_5_c
import FeitThompson.PFsection6.PFsection6_8
import FeitThompson.PFsection9.PFsection9_3
import FeitThompson.PFsection9.PFsection9_4
import FeitThompson.PFsection9.PFsection9_6
public import FeitThompson.PFsection9.PFsection9_11

/-!
# Peterfalvi, Section 10: Theorem (10.5)
-/

noncomputable section

open scoped BigOperators

attribute [local instance] Fintype.ofFinite

namespace Section10
universe u v w

/-! ## (10.5) -/

/-- Peterfalvi `(10.5)`. -/
@[expose] public def theorem_10_5_statement
    {G : Type u} [Group G] [Finite G]
    {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    (M MF W1 W2 : Subgroup G)
    (V : Set G)
    (W : Subgroup M)
    (A A0 : Set M)
    (S : Finset (Section1.ClassFunction M))
    (τ τ₁ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G)
    (ξ : Section1.ClassFunction M)
    (i0 : I)
    (j0 : J)
    (μ : I → J → Section1.ClassFunction M)
    (δSign : J → ℤ)
    (ω : I → J → Section1.ClassFunction W)
    (σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G)
    (d n : ℕ) (δ : ℤ) : Prop :=
  hypothesis_10_4_a_data M MF W1 W2 V W A A0 S τ ξ i0 j0 μ δSign ω σ d n δ →
    ∀ i j, j ≠ j0 →
      Section1.supportedOn (alphaChar μ ξ n δ j0 i j) A0 ∧
        (hypothesis_10_4_data M MF W1 W2 V W A A0 S τ τ₁ ξ i0 j0 μ δSign ω σ d n δ →
          alphaFormulaData W A0 j0 ω σ ξ
            (alphaChar μ ξ n δ j0 i j) i j n δ τ τ₁)

end Section10
