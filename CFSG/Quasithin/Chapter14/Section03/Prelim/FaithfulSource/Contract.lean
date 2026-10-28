module

public import CFSG.Quasithin.Chapter1.Section02.Adequate.Families
public import Theory.SpecificGroups.PSL3Two.Parabolics.LinearModel
public import Mathlib.GroupTheory.SpecificGroups.Alternating

/-!
# The earlier faithful classification consumed in Chapter 14

This interface retains both actual core-quotient isomorphisms, relative
normality in the Sylow join, and maximality in the canonical local family.
Its source proof is supplied by FaithfulSource.Classification. It is placed
below both the HS and later component selections, avoiding an import cycle.
The historical public name is retained for existing consumers.

Source: Aschbacher--Smith, 14.3.4(1--2), printed p.990.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter14.Section04.LargerDimension.LocalAction.Components
open ChapterA.Section04

/-- The universal earlier implication 14.3.4(1--2), in the fixed source
ambient group. Clause (3), about natural modules, is not used in selection.
Both model alternatives and both clauses of (2) are retained. -/
@[expose] def EarlierFaithfulClassification (G : Type*) [Group G] (T : Subgroup G) : Prop :=
  ∀ C : Subgroup G, C ∈ Chapter1.L G T → IsFaithfulSignalizerType C →
    (Nonempty ((C ⧸ pCore 2 C) ≃* alternatingGroup (Fin 5)) ∨
      Nonempty ((C ⧸ pCore 2 C) ≃* Matrix.PSL3Two.PSL)) ∧
    (C.subgroupOf (C ⊔ T)).Normal ∧ C ∈ Chapter1.LStar G T

end CFSG.Quasithin.Chapter14.Section04.LargerDimension.LocalAction.Components
