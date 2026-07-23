module

public import FeitThompson.PFsection8.Basic

/-!
# Peterfalvi, Section 8: Theorem (8.3)
-/

noncomputable section

open scoped BigOperators

attribute [local instance] Fintype.ofFinite

namespace Section8
universe u
universe v
universe w

@[expose] public def definition_8_3_statement
    {G : Type u} [Group G] [Finite G]
    (M MF : Subgroup G) : Prop :=
  section16MFSubgroup M MF ∧ typeIDefinitionData M MF

end Section8
