module
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.TwoFactors.FFBranch.Recognition.ClassificationComparison.QuasisimpleComparison.Targets
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.TwoFactors.FFBranch.Recognition.ClassificationComparison.QuasisimpleComparison.ActorPruning.RankOneRows
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.TwoFactors.FFBranch.Recognition.ClassificationComparison.QuasisimpleComparison.ActorPruning.LastRows

/-!
# The bounded offender-actor comparison

The actual B.5.1 branch splits into the retained actors and two remaining
families. The order and Sylow comparisons exclude both remaining families
from rows (2)–(9), while the defining-prime and Mathieu order calculations
exclude them from rows (10)–(13). Both source orientations are included.
`smallActor_of_bounded` assembles these comparisons without extra row
premises, preserving the original conditional assembly interface.

All maps and actions remain on N = J(D,V) and its original inclusion in D.
In particular the complete corrected module data in `b.source` is retained.
`smallActor_of_quasisimple_source` applies the result to the original
quasisimple source branch via the proved bounded-branch construction.
Source: Aschbacher–Smith, combined manuscript of 1 March 2004, B.5.1/B.5.6,
pp.99–110, F.6.18, pp.309–310, and the FF comparison in 15.4.18, p.1163.
-/

public section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison
open QuasisimpleComparison QuasisimpleComparison.ActorPruning
universe u v

/-- Assemble the smaller actor catalogue from two independent row comparisons.
The rank-one comparison eliminates the earlier rows. The last-four-row
comparison can be proved independently with its row hypothesis explicit. -/
theorem ProjectiveLine.ClassifiedAction.smallActor_of_row_comparisons
    {D : Type u} [Group D] [Finite D] {K : GroupClass.{u}}
    {V : Type v} [AddCommGroup V] [Module (ZMod 2) V]
    {ρ : Representation (ZMod 2) D V} {G₁ G₂ : Subgroup D}
    (h : ProjectiveLine.ClassifiedAction K ρ G₁ G₂)
    (b : BoundedBranch (ρ.comp (offenderSubgroup ρ).subtype))
    (rankOne : RankOneActorModel (offenderSubgroup ρ) → LargeRows G₁ G₂)
    (lastRows : LargeRows G₁ G₂ →
      ¬ RankOneActorModel (offenderSubgroup ρ) ∧
      ¬ LargeActorModel (offenderSubgroup ρ)) :
    SmallActorModel (offenderSubgroup ρ) := by
  rcases actor_split b with ha | ha | ha
  · exact ha
  · exact ((lastRows (rankOne ha)).1 ha).elim
  · exact ((lastRows (h.largeActor_rows ha)).2 ha).elim

/-- Intersect the bounded offender catalogue with all twelve retained
Goldschmidt rows. Both row-comparison premises are discharged on the same
action and its literal normal offender subgroup. The result retains actual
model equivalences, including the perfect triple-six cover. -/
theorem ProjectiveLine.ClassifiedAction.smallActor_of_bounded
    {D : Type u} [Group D] [Finite D] {K : GroupClass.{u}}
    {V : Type v} [AddCommGroup V] [Module (ZMod 2) V]
    {ρ : Representation (ZMod 2) D V} {G₁ G₂ : Subgroup D}
    (h : ProjectiveLine.ClassifiedAction K ρ G₁ G₂)
    (b : BoundedBranch (ρ.comp (offenderSubgroup ρ).subtype)) :
    SmallActorModel (offenderSubgroup ρ) :=
  h.smallActor_of_row_comparisons b (h.rankOneActor_rows b)
    (h.lastRows_not_remainingActors b)

/-- Apply actor pruning to the full corrected B.5.1 branch used in 15.4.18.
The finite model bounds follow from the existing ambient Sylow comparison;
the supplied source conclusion keeps all six module clauses on the original
restricted action for the subsequent fixed-space and extension arguments. -/
theorem ProjectiveLine.ClassifiedAction.smallActor_of_quasisimple_source
    {D : Type u} [Group D] [Finite D] {K : GroupClass.{u}}
    {V : Type v} [AddCommGroup V] [Module (ZMod 2) V]
    {ρ : Representation (ZMod 2) D V} {G₁ G₂ : Subgroup D}
    (h : ProjectiveLine.ClassifiedAction K ρ G₁ G₂)
    (hq : IsQuasisimple (generalizedFitting (offenderSubgroup ρ)))
    (c : FFAlternatives.ProjectiveLine.QuasisimpleSourceConclusion
      (ρ.comp (offenderSubgroup ρ).subtype) (generalizedFitting (offenderSubgroup ρ))) :
    SmallActorModel (offenderSubgroup ρ) := by
  obtain ⟨b⟩ := h.bounded_branch hq c
  exact h.smallActor_of_bounded b

end CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison
