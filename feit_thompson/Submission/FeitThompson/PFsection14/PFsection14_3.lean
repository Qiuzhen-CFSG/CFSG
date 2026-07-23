module

public import Submission.FeitThompson.PFsection14.Basic

/-!
# Peterfalvi, Section 14: Theorem (14.3)
-/

noncomputable section

open scoped BigOperators

attribute [local instance] Fintype.ofFinite

namespace Section14
universe u v w

/-! ## (14.3) -/

/-- Peterfalvi Hypothesis `(14.3)`. -/
@[expose] public def hypothesis_14_3_statement
    {G : Type u} [Group G] [Finite G]
    (Smax Tmax L H P Q U W1 W2 : Subgroup G)
    (Lfam : Finset (Section1.ClassFunction L))
    (RL : G → Subgroup G)
    (τL τL₁ : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G)
    (φ : Section1.ClassFunction L)
    (μ01 : Section1.ClassFunction Smax)
    (ν10 : Section1.ClassFunction Tmax)
    (βS : Section1.ClassFunction Smax)
    (βT : Section1.ClassFunction Tmax)
    (βL : Section1.ClassFunction L) : Prop :=
  hypothesis_14_3_data Smax Tmax L H P Q U W1 W2 Lfam RL τL τL₁ φ μ01 ν10 βS βT βL

end Section14
