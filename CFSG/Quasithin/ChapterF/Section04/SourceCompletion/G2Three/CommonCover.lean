module

public import CFSG.Quasithin.ChapterF.Section04.SourceCompletion.G2Three.Basic
public import Theory.GroupTheory.Amalgam.RankTwoCompletion.OverlapCover

/-!
# The common cover of actual ternary G₂ completions

The proved whole-overlap identity gives the canonical covering from the
universal amalgam completion. Rooted nonbacktracking path transitivity then
agrees with the native octonion model at both vertex types and every length.
In particular the geometric smallness argument may establish its seven-path
input on the native model. That model calculation is not assumed or proved
by the transport equivalence.

Source: Aschbacher–Smith F.3.3–4 and F.4.6(1), printed pp.270–271 and 276.
-/

@[expose] public noncomputable section
namespace CFSG.Quasithin.ChapterF.SourceCompletion.G2Three.Completion
open Theory.GroupTheory
open Subgroup.CosetGeometry.RankTwo
open SimpleGraph.PathTransitivePolygon
variable {G : Type*} [Group G] (c : Completion G)
local notation "α" => GreenBook.LieModels.G2.amalgam (F := ZMod 3)

/-- The actual pushout lift is a covering of the typed coset graphs. -/
theorem coverData : CoverData (RankTwoAmalgam.Universal.cosetFamily α) c.family
    (RankTwoAmalgam.Universal.lift α c) :=
  RankTwoAmalgam.Universal.coverData_of_overlap α c c.overlap

/-- No additional overlap, order, or finiteness premise is needed for transport. -/
theorem rootPathTransitive_iff_model (i : Bool) (n : ℕ) :
    RootPathTransitive c.graph G (base c.family i) n ↔
      RootPathTransitive modelCompletion.graph (Atlas.G2.Model (ZMod 3))
        (base modelCompletion.family i) n :=
  RankTwoAmalgam.Universal.rootPathTransitive_iff_of_overlap α c modelCompletion
    c.overlap model_overlap i n

end CFSG.Quasithin.ChapterF.SourceCompletion.G2Three.Completion
