module

public import FeitThompson.PFsection2.Basic

/-!
# Peterfalvi, Section 2: Theorem (2.8)
-/

noncomputable section

open scoped BigOperators

attribute [local instance] Fintype.ofFinite

namespace Section2
universe u

/-! ## (2.8) -/

@[expose] public def proposition_2_8_statement {G : Type u} [Group G] [Finite G]
    (A : Set G) (L : Subgroup G) (H : G → Subgroup G) : Prop :=
  Hypothesis2 A L H →
    ∀ ⦃B : Set G⦄, B.Nonempty → B ⊆ A →
      IsInternalSemidirectProduct
        (MOfSet H L B) (HInter H B) (normalizerIn L B)

end Section2
