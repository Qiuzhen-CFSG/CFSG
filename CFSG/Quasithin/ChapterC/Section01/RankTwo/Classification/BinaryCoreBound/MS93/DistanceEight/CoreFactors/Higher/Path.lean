module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.CoreFactors.Higher.Assembly

/-!
# The common regular path for the higher-layer constructions

This is the literal standing convention at the start of MS93 (4.5),
printed pp.895--896. Index zero is a-4 and index fourteen is a+10.
The record retains the walk, all local turns, all four critical windows,
and the unequal adjacent Z-layers. It contains no higher-layer conclusion.

Both independent higher-layer constructions can take the same path as input.
Constructing this path belongs to the preceding early-layer argument. In
particular, the record is not an existence theorem from Earlier.extended.
The distance calculations below apply its walk to the published hat layers.
-/

@[expose] public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.CoreFactors.Higher
variable {M : Type*} [Group M] {R : Subgroup M}

/-- The complete standing path convention of (4.5), specialized to b=8. -/
structure SourcePath (a : Vertex R) where
  first : Vertex R
  last : Vertex R
  walk : (cosetGraph R).Walk first last
  start_color : color R first = false
  length_eq : walk.length = 14
  shortest : walk.length = (cosetGraph R).dist first last
  center_eq : walk.getVert 4 = a
  turns : ∀ i : ℕ, Even i → 2 ≤ i → i ≤ 12 →
    ∃ g ∈ stabilizer R (walk.getVert i),
      act R g (walk.getVert (i + 2)) = walk.getVert (i - 2)
  critical : ∀ i : ℕ, Even i → i ≤ 6 →
    (cosetGraph R).dist (walk.getVert i) (walk.getVert (i + 8)) = 8 ∧
      ¬ Z R (walk.getVert i) ≤ Q R (walk.getVert (i + 8))
  distinct_Z : ∀ i : ℕ, Even i → 2 ≤ i → i ≤ 12 →
    Z R (walk.getVert (i - 1)) ≠ Z R (walk.getVert (i + 1))

namespace SourcePath
variable {a : Vertex R} (p : SourcePath a)

/-- Distances between actual vertices of the supplied regular path. -/
theorem dist {i j : ℕ} (hij : i ≤ j) (hj : j ≤ 14) :
    (cosetGraph R).dist (p.walk.getVert i) (p.walk.getVert j) = j - i := by
  have hsub := ((p.walk.drop i).isSubwalk_take (j - i)).trans (p.walk.isSubwalk_drop i)
  have h := SimpleGraph.length_eq_dist_of_subwalk p.shortest hsub
  have hle : j - i ≤ p.walk.length - i := by rw [p.length_eq]; omega
  simpa only [SimpleGraph.Walk.take_length, SimpleGraph.Walk.drop_length,
    inf_eq_left.mpr hle, SimpleGraph.Walk.drop_getVert, Nat.add_sub_of_le hij] using h.symm

/-- The three source steps used by the hat Six definition each have length two. -/
theorem two_step_distances :
    (cosetGraph R).dist (p.walk.getVert 6) a = 2 ∧
      (cosetGraph R).dist (p.walk.getVert 8) (p.walk.getVert 6) = 2 ∧
      (cosetGraph R).dist (p.walk.getVert 10) (p.walk.getVert 8) = 2 := by
  refine ⟨?_, ?_, ?_⟩
  · simpa only [p.center_eq, SimpleGraph.dist_comm] using
      p.dist (i := 4) (j := 6) (by decide) (by decide)
  · rw [SimpleGraph.dist_comm]
    exact p.dist (by decide) (by decide)
  · rw [SimpleGraph.dist_comm]
    exact p.dist (by decide) (by decide)

/-- A consumer at the actual vertices a+2, a+4, a+6 of the common source path. -/
theorem hatSix_le_Q {geometry : Geometry R} (earlier : Earlier R geometry) :
    hatSix R a (p.walk.getVert 6) (p.walk.getVert 8) (p.walk.getVert 10) ≤ Q R a := by
  have ha : color R a = false := by
    rw [← p.center_eq]
    exact (PathCentrality.RegularPaths.walk_vertex_color p.start_color p.walk
      (by rw [p.length_eq]; decide)).mpr (by decide)
  exact Higher.hatSix_le_Q earlier ha p.two_step_distances.1.le
    p.two_step_distances.2.1.le p.two_step_distances.2.2.le

end SourcePath
end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.CoreFactors.Higher
