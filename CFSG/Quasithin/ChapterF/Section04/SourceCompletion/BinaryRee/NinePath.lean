module
public import CFSG.Quasithin.ChapterF.Section04.SourceCompletion.BinaryRee.NinePathRegular
public import Theory.SpecificGroups.ReeF4.Octagon.Binary.RootPaths
/-!
# Nine-path rigidity in every faithful full binary Ree completion

The actual binary Ree octagonal BN-pair supplies nine-path transitivity at
both prescribed local groups. The common pushout covers transfer it to every
vertex of the original source completion. Exact path counts make these actions
regular and force every sixteen-cycle to have trivial pointwise fixer.

All model and transport premises are discharged here. No smallness, global
recognition, or braid relation is used for these local path conclusions.

Source: Aschbacher--Smith, F.4.6 and F.4.15--16, printed pp.276--277 and 281--282.
-/

@[expose] public section
noncomputable section
namespace CFSG.Quasithin.ChapterF.SourceCompletion.BinaryRee.Completion
open Subgroup.CosetGeometry.RankTwo
open SimpleGraph SimpleGraph.PathTransitivePolygon
variable {G : Type*} [Group G] (c : Completion G)

/-- Both types in every faithful full Ree completion are nine-path transitive,
by the actual octagonal BN-pair and the marked common-pushout coverings. -/
theorem nine_transitive (v : c.Vertex) : RootPathTransitive c.graph G v 9 := by
  apply all_rootPathTransitive_of_model c 9
  intro i
  have hf : modelFamily = ReeF4.Octagon.Binary.family := by
    funext b
    cases b <;> rfl
  rw [hf]
  exact ReeF4.Octagon.Binary.both_base_rootPathTransitive_nine i

/-- The actual nine-path action is regular, without a transitivity premise. -/
theorem nine_fixer_eq_bot (v : c.Vertex) (p : BasedWalk c.graph 9 v)
    (hp : p.Nonbacktracking) : pathStabilizer c.family p = ⊥ :=
  nine_pathStabilizer_eq_bot c v (nine_transitive c v) p hp

/-- Every actual apartment has faithful setwise-stabilizer action. -/
theorem apartment_fixer_eq_bot (v : c.Vertex) (p : c.graph.Walk v v)
    (hp : p.IsCycle) (hlen : p.length = 16) :
    fixingSubgroup G {w | w ∈ p.support} = ⊥ :=
  cycle_fixer_eq_bot c v (nine_transitive c v) p hp hlen
end CFSG.Quasithin.ChapterF.SourceCompletion.BinaryRee.Completion
