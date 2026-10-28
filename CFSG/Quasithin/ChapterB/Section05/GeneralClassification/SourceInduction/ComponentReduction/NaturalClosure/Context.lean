module

public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.ComponentReduction.Statement
public import Theory.GroupTheory.PResidual.PrimeTo

/-!
# Interfaces for the two-component argument of B.5.9

The setup contains the original finite faithful FF action, the chosen minimal
offender, the preceding component normality and three-rank conclusions, and
the universally quantified preliminary action theorem. The latter is the
explicit intermediate input permitted for this branch; its producer is
`qt-b05-component-preliminary-actions`.

`SecondComponent` specifies the group-theoretic output when the seed is
properly contained in the moved space. It keeps the second actual component,
its own natural seed, the placement of A, the nontrivial cross action and
the genuine prime-to-three residual. These are targets, not assumed earlier
source theorems. Construction and exclusion of this configuration are the
two remaining parts of the natural-closure proof.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, B.5.9,
printed p.108, beginning of the final paragraph.
-/

@[expose] public section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
namespace CFSG.Quasithin.ChapterB.SourceInduction.ComponentReduction.NaturalClosure
open QuasisimpleSource
universe u v
variable {G : Type u} [Group G] [Finite G]
  {V : Type v} [AddCommGroup V] [Module (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V)

/-- The source setup before enlarging a natural seed. No closure or numerical
estimate is included. Final assembly must supply the preliminary theorem. -/
structure Setup (K : GroupClass.{u}) (A : Subgroup G) : Prop where
  hypothesis : FFHypothesis K ρ
  minimal : IsMinimalBestOffender ρ A
  centralizes_fitting : A ≤ centralizer (fittingSubgroup G : Set G)
  component_normal : ∀ M, IsComponent G M → M.Normal
  component_three_rank : ∀ M, IsComponent G M → primeRank 3 M = 1
  preliminary : ∀ M, IsComponent G M → ⁅M, A⁆ = M →
    ∀ s : MovedSection ρ M, PreliminaryConclusion ρ A M s

/-- The actual second-component configuration to construct and then exclude.
The field degree is not ordered; the exclusion may choose the larger one. -/
structure SecondComponent (A L : Subgroup G) where
  second : Subgroup G
  isComponent : IsComponent G second
  distinct : L ≠ second
  commutator_eq : ⁅second, A⁆ = second
  seed : NaturalSeed ρ A second
  offender_le : A ≤ L ⊔ second
  residual_eq : L ⊔ second =
    (primeToResidual 3 ↥(componentLayer G)).map (componentLayer G).subtype
  cross_action : subspaceCommutator ρ (moved ρ L) second ≠ ⊥

end CFSG.Quasithin.ChapterB.SourceInduction.ComponentReduction.NaturalClosure
