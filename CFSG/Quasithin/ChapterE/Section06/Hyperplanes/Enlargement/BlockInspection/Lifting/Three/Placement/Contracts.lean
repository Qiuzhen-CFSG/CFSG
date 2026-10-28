module

public import CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.BlockInspection.Lifting.Three.Placement.Reduction

/-!
# The two mixed-component action obligations

These are independent new obligations in the solvable A₃ repair, not earlier
source results. The reduction to these model families and the exact fixed
space is proved in `Reduction`. Each obligation must control the original
block's action on an arbitrary component in its family. Containment in that
component is an allowed conclusion, never a premise.

The Borel family retains the central two-covers of PSL₃(4); the symplectic
family retains the binary derived endpoint and the parameter-four root
action. Ordinary relative component membership and the literal block module
are used throughout. A proof using A₄ must construct that identification.

Source: the missing solvable localization in Aschbacher–Smith E.6.23,
printed p.254 (PDF p.265), with the model list in E.6.8, pp.247–248.
-/

@[expose] public section

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.BlockInspection.Lifting.Three.Placement
open ComponentBalance Components

variable {G : Type*} [Group G]

/-- Mixed action on a parameter-four Borel component. The actual Borel and
V-action are retained, including the possibility of a central two-cover. -/
def BorelInteraction (M V : Subgroup G) : Prop :=
  ∀ U ∈ obstructionFamily M V, IsHyperplane V U →
    ∀ L : Subgroup G, SmallBlock U L → ChapterC.IsAlternatingBlock L 3 → (¬ L ≤ M) →
      ∀ A ∈ obstructionFamily M V, A ≤ U → subgroupCorank V A = 2 →
        ∀ X : Subgroup G, CentralizerComponent A X →
          V ⊓ centralizer (X : Set G) = A → BorelAlternative M V A X 2 →
            L ≤ X ∨ ⁅L, X⁆ = ⊥

/-- Mixed action on the binary derived symplectic component or the
parameter-four component with its actual root action. -/
def SymplecticInteraction (M V : Subgroup G) : Prop :=
  ∀ U ∈ obstructionFamily M V, IsHyperplane V U →
    ∀ L : Subgroup G, SmallBlock U L → ChapterC.IsAlternatingBlock L 3 → (¬ L ≤ M) →
      ∀ A ∈ obstructionFamily M V, A ≤ U → subgroupCorank V A = 2 →
        ∀ X : Subgroup G, CentralizerComponent A X →
          V ⊓ centralizer (X : Set G) = A →
            (SymplecticAlternative M V A X 1 ∨
              (SymplecticAlternative M V A X 2 ∧
                MaximalParabolic X (X ⊓ M) ∧ SymplecticRootAction X V 2)) →
                  L ≤ X ∨ ⁅L, X⁆ = ⊥

end CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.BlockInspection.Lifting.Three.Placement
