module

public import FeitThompson.PFsection14.Basic

/-!
# Peterfalvi, Section 14: Theorem (14.10)
-/

noncomputable section

open scoped BigOperators

attribute [local instance] Fintype.ofFinite

namespace Section14
universe u v w

/-! ## (14.10) -/

/-- Peterfalvi Hypothesis `(14.10)`. -/
@[expose] public def hypothesis_14_10_statement
    {G : Type u} [Group G] [Finite G]
    (M K V : Subgroup G)
    (Mfam : Finset (Section1.ClassFunction M))
    (τM τM₁ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G)
    (ψ : Section1.ClassFunction M)
    (βM : Section1.ClassFunction M) : Prop :=
  hypothesis_14_10_data M K V Mfam τM τM₁ ψ βM

end Section14
