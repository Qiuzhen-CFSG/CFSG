module

public import CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.BlockInspection.ComponentCase.Reduction

/-!+# The two remaining intrinsic inspections in E.6.23

The fixed-space reduction, PSL₂(4) exclusion, binary symplectic identification,
and relative normality in A₆ leave two independent model calculations.
These definitions specify outstanding obligations, not source theorems.
The final assembly constructs their extra fixed-space premise.

Both contracts retain the actual embedded block and its conjugation module,
as well as all the actions in the E.6.8 alternative. In particular the first
contract includes every central two-cover of PSL₃(4). Neither contract assumes
that the block is normal in the component's centralizer.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), E.6.23,
printed p.254 (PDF p.265), with the full E.6.8 alternatives on pp.247–248.
-/

@[expose] public section

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.BlockInspection.ComponentCase
open ComponentBalance Components

variable {G : Type*} [Group G]

/-- Exclude the three-dimensional Borel models at parameter four, including
their central two-covers, from containing the actual small block. -/
def ThreeDimensionalExclusion (M V : Subgroup G) : Prop :=
  ∀ U ∈ obstructionFamily M V, IsHyperplane V U →
    ∀ L : Subgroup G, SmallBlock U L → (¬ L ≤ M) →
      ∀ A ∈ obstructionFamily M V, A ≤ U → subgroupCorank V A = 2 →
        ∀ X : Subgroup G, L < X → CentralizerComponent A X →
          V ⊓ centralizer (X : Set G) = A → BorelAlternative M V A X 2 →
          (ClassicalGroup.IsPSL X 3 4 ∨ ClassicalGroup.IsPSU X 3 4 ∨
            (IsPGroup 2 (center X) ∧ ClassicalGroup.IsPSL (X ⧸ center X) 3 4)) → False

/-- Exclude the nonbinary symplectic root-action branch. The full alternative
retains the actual field, derived-group equivalence, and marked root action. -/
def SymplecticFourExclusion (M V : Subgroup G) : Prop :=
  ∀ U ∈ obstructionFamily M V, IsHyperplane V U →
    ∀ L : Subgroup G, SmallBlock U L → (¬ L ≤ M) →
      ∀ A ∈ obstructionFamily M V, A ≤ U → subgroupCorank V A = 2 →
        ∀ X : Subgroup G, L < X → CentralizerComponent A X →
          V ⊓ centralizer (X : Set G) = A → SymplecticAlternative M V A X 2 →
          MaximalParabolic X (X ⊓ M) → SymplecticRootAction X V 2 → False

end CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.BlockInspection.ComponentCase
