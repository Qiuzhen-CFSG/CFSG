module

public import CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.BlockInspection.Lifting.SourceInputs

/-!
# The remaining two branches of corank-two lifting

These are outstanding proof obligations, not earlier-source theorems.
The solvable branch requires an argument independent of 1.2.4. The other
obligation classifies a constructed, escaping C-component once its
overgroup generated with Q is known to have characteristic two.
It must establish the block type and module; the generalized Fitting
equality alone is not an identification with a block.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), E.6.23,
printed p.254, using E.6.7, p.246, and 1.2.4, p.505.
-/

@[expose] public section

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.BlockInspection.Lifting
open ComponentBalance

variable {G : Type*} [Group G]

/-- The solvable A₃ branch. Its proof must not use membership in the
perfect C-component family or assume block persistence. -/
def ThreeBlockLifting (M V : Subgroup G) : Prop :=
  ∀ U ∈ obstructionFamily M V, IsHyperplane V U →
    ∀ L : Subgroup G, SmallBlock U L → ChapterC.IsAlternatingBlock L 3 → (¬ L ≤ M) →
      ∀ A ∈ obstructionFamily M V, A ≤ U → subgroupCorank V A = 2 →
        ∃ X : Subgroup G, L ≤ X ∧
          ((CentralizerBlock A X ∧ ChapterC.IsChiZeroBlock X) ∨ CentralizerComponent A X)

/-- The characteristic-two branch for a genuine escaping C-component,
where Q is the common Sylow subgroup. This is a new local obligation,
not an assumption disguised as E.6.7. -/
def CharacteristicTwoComponentBlocks (Q M V : Subgroup G) : Prop :=
  ∀ A ∈ obstructionFamily M V, subgroupCorank V A = 2 →
    ∀ X : Subgroup G, X ∈ Chapter1.cComponentsIn (centralizer (A : Set G)) →
      (¬ X ≤ M) → generalizedFitting ↥(X ⊔ Q) = pCore 2 ↥(X ⊔ Q) →
        CentralizerBlock A X ∧ ChapterC.IsChiZeroBlock X

end CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.BlockInspection.Lifting
