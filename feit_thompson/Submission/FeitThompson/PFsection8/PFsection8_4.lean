module

public import FeitThompson.PFsection8.Basic

/-!
# Peterfalvi, Section 8: Theorem (8.4)
-/

noncomputable section

open scoped BigOperators

attribute [local instance] Fintype.ofFinite

namespace Section8
universe u
universe v
universe w

@[expose] public def definition_8_4_statement
    {G : Type u} [Group G] [Finite G]
    (M MF U W1 W2 : Subgroup G) : Prop :=
  typePDefinitionData M MF U W1 W2

end Section8
