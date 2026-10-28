module

public import CFSG.Quasithin.ChapterF.Section04.SourceCompletion.LinearThreeFour.Smallness.Local
public import Theory.GroupTheory.Amalgam.RankTwoCompletion.Universal
public import Theory.GroupAction.RankTwoCosetCover.RootPathTransitivity

/-!
# The common cover for the PSL₃(4) flag amalgam

The proved whole-overlap identity applies also to the universal completion.
Its canonical homomorphism to any faithful completion therefore gives an
actual coset covering, including local injectivity. These coverings transfer
rooted nonbacktracking path transitivity from the native model at every length.
The equal endpoint orders cause no coprime-index assumption.

Source: Aschbacher–Smith F.3.3–4 and F.4.6(1), printed pp.270–271, 276.
-/

@[expose] public noncomputable section
namespace CFSG.Quasithin.ChapterF.SourceCompletion.LinearThreeFour
open Theory.GroupTheory
open Subgroup.CosetGeometry.RankTwo
open SimpleGraph.PathTransitivePolygon

local notation "α" => GreenBook.LieModels.LinearThree.amalgam Matrix.PSL3Four.F

def universalCompletion : Completion (RankTwoAmalgam.Universal α) :=
  RankTwoAmalgam.Universal.completion α modelCompletion

namespace Completion
variable {G : Type*} [Group G] (c : Completion G)

/-- The canonical pushout map, with the literal cosets and whole overlap. -/
theorem coverData : CoverData universalCompletion.family c.family
    (RankTwoAmalgam.Universal.lift α c) where
  surjective := RankTwoAmalgam.Universal.lift_surjective α c
  map_eq i := by
    cases i
    · exact RankTwoAmalgam.Universal.map_left_range α c
    · exact RankTwoAmalgam.Universal.map_right_range α c
  injective i := by
    cases i
    · exact RankTwoAmalgam.Universal.injective_on_left α c
    · exact RankTwoAmalgam.Universal.injective_on_right α c
  map_inf := by
    change (universalCompletion.left.range ⊓ universalCompletion.right.range).map _ =
      c.left.range ⊓ c.right.range
    rw [universalCompletion.overlap, c.overlap]
    exact RankTwoAmalgam.Universal.map_middle_range α c

/-- The model and arbitrary completion have identical rooted path transitivity. -/
theorem rootPathTransitive_iff_model (i : Bool) (n : ℕ) :
    RootPathTransitive c.graph G (base c.family i) n ↔
      RootPathTransitive modelCompletion.graph Matrix.PSL3Four.PSL
        (base modelCompletion.family i) n := by
  constructor
  · intro ht
    have h : RootPathTransitive c.graph G
        (c.coverData.vertex (base universalCompletion.family i)) n := by
      simpa only [CoverData.vertex_base] using ht
    simpa only [CoverData.vertex_base] using
      c.coverData.transport_rootPathTransitive modelCompletion.coverData n
        (base universalCompletion.family i) h
  · intro ht
    have h : RootPathTransitive modelCompletion.graph Matrix.PSL3Four.PSL
        (modelCompletion.coverData.vertex (base universalCompletion.family i)) n := by
      simpa only [CoverData.vertex_base] using ht
    simpa only [CoverData.vertex_base] using
      modelCompletion.coverData.transport_rootPathTransitive c.coverData n
        (base universalCompletion.family i) h

end Completion
end CFSG.Quasithin.ChapterF.SourceCompletion.LinearThreeFour
