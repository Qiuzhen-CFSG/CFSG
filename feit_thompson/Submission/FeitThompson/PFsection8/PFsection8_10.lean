module

public import FeitThompson.PFsection8.Basic

/-!
# Peterfalvi, Section 8: Theorem (8.10)
-/

noncomputable section

open scoped BigOperators

attribute [local instance] Fintype.ofFinite

namespace Section8
universe u
universe v
universe w

@[expose] public def definition_8_10_statement
    {G : Type u} [Group G] [Finite G]
    (M MF Ms : Subgroup G)
    (A A0 A1 : Set G) : Prop :=
  notation_8_10_literal_source_data M MF Ms A A0 A1

end Section8
