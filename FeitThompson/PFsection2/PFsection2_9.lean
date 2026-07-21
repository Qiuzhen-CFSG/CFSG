module

public import FeitThompson.PFsection2.Basic

/-!
# Peterfalvi, Section 2: Theorem (2.9)
-/

noncomputable section

open scoped BigOperators

attribute [local instance] Fintype.ofFinite

namespace Section2
universe u

/-! ## (2.9) -/

@[expose] public def notation_2_9_statement {G : Type u} [Group G] [Finite G]
    (A : Set G) (L : Subgroup G) [Finite L] (H : G → Subgroup G)
    (_h : Hypothesis2 A L H) (α : Section1.ClassFunction L) : Prop :=
  CFOn L A α →
    ∀ ⦃B : Set G⦄, B.Nonempty → B ⊆ A →
      ∃ αB : Section1.ClassFunction (MOfSet H L B),
        alphaBSpec H α B αB ∧
          (Representation.IsVirtualCharacter α →
            Representation.IsVirtualCharacter αB)

end Section2
