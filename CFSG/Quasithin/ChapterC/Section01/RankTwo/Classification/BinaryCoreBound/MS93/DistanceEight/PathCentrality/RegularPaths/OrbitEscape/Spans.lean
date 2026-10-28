module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.PathCentrality.RegularPaths.Basic
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Setup.NormalizerTransfer

/-!
# The two orbit spans in the MS93 escape argument

The forward span V and reverse span V₁ are subgroups of the start stabilizer.
Each lies in its center vertex's kernel, which fixes the other vertex at
distance two. Thus each span normalizes the other, and their join is the
literal subgroup product V V₁. Its normality in the full start stabilizer
is a further source obligation, not a consequence asserted here.

Source: Meierfrankenfeld--Stellmacher, Pushing up weak BN-pairs of rank two
(1993), (4.4.2), printed pp.892--893.
-/

@[expose] public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality.RegularPaths.OrbitEscape
variable {M : Type*} [Group M] {R : Subgroup M} {geometry : Geometry R}

open scoped Pointwise

/-- The subgroup product V V₁ in (4.4.2), initially expressed as a join. -/
noncomputable def jointSpan {a a' : Vertex R} (p : CriticalPath R geometry a a') :
    Subgroup (FreeAmalgam R) :=
  localZSpan R (p.walk.getVert 2) a ⊔ localZSpan R a (p.walk.getVert 2)

/-- Both spans lie in the actual local stabilizer, using distance-two kernel fixation. -/
theorem jointSpan_le_stabilizer [Finite M] {a a' : Vertex R}
    (p : CriticalPath R geometry a a') (hb : 2 < geometry.b R) :
    jointSpan p ≤ stabilizer R a := by
  have hd : (cosetGraph R).dist a (p.walk.getVert 2) = 2 :=
    p.dist_start (by have hh := p.length_eq_b; omega)
  have hc : color R (p.walk.getVert 2) = false :=
    (p.vertex_color (by have hh := p.length_eq_b; omega)).mpr (by decide)
  apply sup_le
  · exact (localZSpan_le_Q R p.start_color (by rw [SimpleGraph.dist_comm, hd]) hb).trans
      (fun _ hx => hx.1)
  · exact (localZSpan_le_Q R hc hd.le hb).trans
      (Q_le_stabilizer_of_dist_two R _ _ hc (by rw [SimpleGraph.dist_comm, hd]))

/-- The two spans normalize each other; this does not assert normalization by G_a. -/
theorem spans_mutually_normalize [Finite M] {a a' : Vertex R}
    (p : CriticalPath R geometry a a') (hb : 2 < geometry.b R) :
    localZSpan R (p.walk.getVert 2) a ≤ normalizer (localZSpan R a (p.walk.getVert 2)) ∧
    localZSpan R a (p.walk.getVert 2) ≤ normalizer (localZSpan R (p.walk.getVert 2) a) := by
  have hd : (cosetGraph R).dist a (p.walk.getVert 2) = 2 :=
    p.dist_start (by have hh := p.length_eq_b; omega)
  have hc : color R (p.walk.getVert 2) = false :=
    (p.vertex_color (by have hh := p.length_eq_b; omega)).mpr (by decide)
  constructor
  · exact (localZSpan_le_Q R p.start_color (by rw [SimpleGraph.dist_comm, hd]) hb).trans
      ((Q_le_stabilizer_of_dist_two R _ _ p.start_color hd).trans
        (localZSpan_normalized R a (p.walk.getVert 2)))
  · exact (localZSpan_le_Q R hc hd.le hb).trans
      ((Q_le_stabilizer_of_dist_two R _ _ hc (by rw [SimpleGraph.dist_comm, hd])).trans
        (localZSpan_normalized R (p.walk.getVert 2) a))

/-- The join is the literal product used on printed p.893. -/
theorem jointSpan_eq_product [Finite M] {a a' : Vertex R}
    (p : CriticalPath R geometry a a') (hb : 2 < geometry.b R) :
    (↑(jointSpan p) : Set (FreeAmalgam R)) =
      (localZSpan R (p.walk.getVert 2) a : Set (FreeAmalgam R)) *
        (localZSpan R a (p.walk.getVert 2) : Set (FreeAmalgam R)) :=
  coe_mul_of_left_le_normalizer_right _ _ (spans_mutually_normalize p hb).1

/-- Normality is relative to G_a, and is equivalent to its normalizer containment. -/
theorem jointSpan_normal_iff [Finite M] {a a' : Vertex R}
    (p : CriticalPath R geometry a a') (hb : 2 < geometry.b R) :
    ((jointSpan p).subgroupOf (stabilizer R a)).Normal ↔
      stabilizer R a ≤ normalizer (jointSpan p) := by
  exact normal_subgroupOf_iff_le_normalizer (jointSpan_le_stabilizer p hb)

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality.RegularPaths.OrbitEscape
