module

public import FeitThompson.PFsection8.Basic

/-!
# Peterfalvi, Section 8: Theorem (8.14)
-/

noncomputable section

open scoped BigOperators

attribute [local instance] Fintype.ofFinite

namespace Section8
universe u
universe v
universe w

@[expose] public def definition_8_14_statement
    {G : Type u} [Group G] [Finite G]
    (M MF Ms : Subgroup G)
    (A A0 A1 D tildeA tildeA0 tildeA1 : Set G)
    (R : G → Subgroup G) : Prop :=
  notation_8_10_source_data M MF Ms A A0 A1 ∧
    notation_8_14_source_data M A A0 A1 D tildeA tildeA0 tildeA1 R

end Section8
