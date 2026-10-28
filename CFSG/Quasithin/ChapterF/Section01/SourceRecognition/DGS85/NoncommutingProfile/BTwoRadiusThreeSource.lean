module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.NoncommutingProfile.BOneTreeSource
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.ApartmentExchange.ReflectionPaths
public import Theory.GroupAction.RankTwoCosetGeometry.Kernels
public import Theory.GroupTheory.WeakBNPair.RegularTree.RadiusThreeCover
public import Theory.GroupTheory.WeakBNPair.RegularTree.PathRootCover

/-!
# Lifting the central radius-three cover to the universal source tree

The reduced F.1.1 covering lifts a radius-two fixer at each neighbor of a
marked endpoint.  The elementary neighboring-ball cover then gives the
radius-three fixer at that endpoint on the literal universal tree.  The
target premises are stated as the actual `ballKernel`s of the reduced family;
no b=1 local profile is used.
-/

public section
open Subgroup Theory.GroupTheory RankTwoAmalgam
open Theory.GroupTheory.WeakBNPair.RegularTree Subgroup.CosetGeometry
open Subgroup.CosetGeometry.RankTwo
open CFSG.Quasithin.ChapterF.Source.DGS85.Reduction
open CFSG.Quasithin.ChapterF.Source
open CFSG.Quasithin.ChapterF.Source.DGS85.OriginalExtension
open CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.ApartmentExchange
namespace CFSG.Quasithin.ChapterF.Source.DGS85.NoncommutingProfile
variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}

/-- Lift neighboring reduced radius-two fixers to the radius-three ball of the
marked universal endpoint. -/
theorem source_radius_three_of_neighbor_ball
    (h : HypothesisF11 L S) (i : Bool)
    (z : (reducedAmalgam L S).Universal)
    (hz : z • Subgroup.CosetGeometry.RankTwo.base
      (Universal.cosetFamily (reducedAmalgam L S)) i =
      Subgroup.CosetGeometry.RankTwo.base
        (Universal.cosetFamily (reducedAmalgam L S)) i)
    (hN : ∀ v, (sourceGraph (reducedAmalgam L S)).Adj
        (Subgroup.CosetGeometry.RankTwo.base
          (Universal.cosetFamily (reducedAmalgam L S)) i) v →
      bOne_tree_map h z ∈ Subgroup.CosetGeometry.RankTwo.ballKernel (reducedFamily L S)
        ((bOne_tree_cover h).vertex v) 2)
    (hzN : ∀ v, (sourceGraph (reducedAmalgam L S)).Adj
        (Subgroup.CosetGeometry.RankTwo.base
          (Universal.cosetFamily (reducedAmalgam L S)) i) v → z • v=v) :
    z ∈ graphBallFixer (sourceGraph (reducedAmalgam L S))
      (Subgroup.CosetGeometry.RankTwo.base
        (Universal.cosetFamily (reducedAmalgam L S)) i) 3 := by
  apply graphBallFixer_radius_three_of_neighbor (sourceGraph (reducedAmalgam L S))
    (Subgroup.CosetGeometry.RankTwo.base
      (Universal.cosetFamily (reducedAmalgam L S)) i) z hz
  intro v hv
  have hl := (bOne_tree_cover h).ballKernel_lift v 2 z (hzN v hv) (hN v hv)
  rw [mem_graphBallFixer]
  intro w hw
  exact hl w hw

end CFSG.Quasithin.ChapterF.Source.DGS85.NoncommutingProfile
