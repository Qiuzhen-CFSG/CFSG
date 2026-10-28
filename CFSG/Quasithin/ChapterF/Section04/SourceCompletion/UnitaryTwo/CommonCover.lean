module
public import CFSG.Quasithin.ChapterF.Section04.SourceCompletion.UnitaryTwo
public import CFSG.Quasithin.ChapterF.Section04.SourceCompletion.UnitaryTwo.Extension
public import Theory.GroupTheory.Amalgam.RankTwoCompletion.CommonCover
/-!
# Common covers for the ordinary and extended binary unitary amalgams

The literal inclusions in U₄(2), and in its specified graph extension, are
faithful completions. Comparing them with an arbitrary completion through
the actual amalgamated product transfers rooted path transitivity in both
directions, at both marked vertex types and every length.

This proves the transfer portion of Aschbacher–Smith F.4.6(1), printed p.276.
The native model's five-path transitivity, and the subsequent quadrangle
recognition in F.4.24, are distinct mathematical assertions.
-/
@[expose] public noncomputable section
namespace CFSG.Quasithin.ChapterF.SourceCompletion.UnitaryTwo
open Theory.GroupTheory
open Subgroup.CosetGeometry.RankTwo
open SimpleGraph.PathTransitivePolygon
local notation "h1" => (Nat.le_refl 1)

def modelCompletion : Completion (GreenBook.LieModels.UnitaryFour.ProjectiveGroup 1 h1) :=
  RankTwoAmalgam.FaithfulCompletion.ofSubgroups _ _ _
    (Subgroup.map_mono inf_le_left) (Subgroup.map_mono inf_le_right)
    (GreenBook.LieModels.UnitaryFour.parabolics_generate 1 h1)

theorem Completion.rootPathTransitive_iff_model {G : Type*} [Group G]
    (c : Completion G) (i : Bool) (n : ℕ) :
    RootPathTransitive c.graph G (base c.family i) n ↔
      RootPathTransitive modelCompletion.graph
        (GreenBook.LieModels.UnitaryFour.ProjectiveGroup 1 h1)
        (base modelCompletion.family i) n := by
  apply RankTwoAmalgam.Universal.rootPathTransitive_iff
  rw [GreenBook.LieModels.UnitaryFour.BinaryCompletion.point_card,
    GreenBook.LieModels.UnitaryFour.BinaryCompletion.plane_card,
    GreenBook.LieModels.UnitaryFour.BinaryCompletion.middle_card]
  norm_num

namespace Extension

def modelCompletion : Completion
    (GreenBook.LieModels.UnitaryFour.Extension.ProjectiveExtension 1 h1) :=
  RankTwoAmalgam.FaithfulCompletion.ofSubgroups _ _ _
    (Subgroup.map_mono inf_le_left) (Subgroup.map_mono inf_le_right)
    GreenBook.LieModels.UnitaryFour.Extension.binary_parabolics_generate

theorem Completion.rootPathTransitive_iff_model {G : Type*} [Group G]
    (c : Completion G) (i : Bool) (n : ℕ) :
    RootPathTransitive c.graph G (base c.family i) n ↔
      RootPathTransitive modelCompletion.graph
        (GreenBook.LieModels.UnitaryFour.Extension.ProjectiveExtension 1 h1)
        (base modelCompletion.family i) n := by
  apply RankTwoAmalgam.Universal.rootPathTransitive_iff
  rw [GreenBook.LieModels.UnitaryFour.Extension.binary_point_card,
    GreenBook.LieModels.UnitaryFour.Extension.binary_plane_card,
    GreenBook.LieModels.UnitaryFour.Extension.binary_overlap_card]
  norm_num
end Extension
end CFSG.Quasithin.ChapterF.SourceCompletion.UnitaryTwo
