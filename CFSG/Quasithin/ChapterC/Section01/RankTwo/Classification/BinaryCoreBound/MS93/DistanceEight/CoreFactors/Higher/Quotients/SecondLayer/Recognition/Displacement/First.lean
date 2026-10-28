module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.CoreFactors.Higher.Quotients.SecondLayer.Recognition.Displacement.Transfer
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.CoreFactors.Higher.OrbitGeometry.TwoCases.ZGeometry.NeighborAction.Geometry

/-!
# The first actual orbit factor: the forward small actor

The actor is hat W at indices 8,10,12 of the supplied source path.
The turn at index 8 and the literal first-layer identities compare it
with the backward product from (4.5.1)(iv). Its original projection image
is therefore the image of the edge kernel at index 5.

The (4.5.4)(ii) containment and (4.5.3)(ii) commutator put displacement
inside Z at index 8. The edge at index 7 supplies index at most two after
quotienting by the actual denominator. Transfer then compares this with
order four on common.natural, with exactly its original marking.

The explicit first-layer identities, backward product and commutator
are literal translated (4.5.1)--(4.5.3) conclusions, produced by
qt-c01-ms93-core-factors-early-layers. Orbit containment is (4.5.4)(ii),
produced by qt-c01-ms93-higher-orbit-geometry. The recognition assembly
must supply these earlier-source premises; no later quotient is used.
Source: Meierfrankenfeld--Stellmacher (1993), printed pp.896--899.
-/

public section
open Subgroup Stellmacher.PushingUp.AmalgamGraph
open scoped commutatorElement Pointwise
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.CoreFactors.Higher.Quotients.SecondLayer.Recognition.Displacement
variable {M : Type*} [Group M] {R L : Subgroup M}

private theorem path_color (p : Higher.SourcePath (alpha R))
    {i : ℕ} (hi : Even i) (hle : i ≤ 14) : color R (p.walk.getVert i) = false :=
  (PathCentrality.RegularPaths.walk_vertex_color p.start_color p.walk
    (by rw [p.length_eq]; exact hle)).mpr hi

/-- The forward actor on p.899 is the actual hat W at indices 8,10,12.
The turn at index 8 compares it with the backward instance of (4.5.1)(iv).
All three displayed first-layer equalities are literal (4.5.3)(i) instances. -/
theorem first_actor_product (p : Higher.SourcePath (alpha R))
    (hV6 : hatV R (p.walk.getVert 6) (p.walk.getVert 8) =
      Vcirc R (p.walk.getVert 6) ⊔ Z R (p.walk.getVert 6))
    (hV6rev : hatV R (p.walk.getVert 6) (p.walk.getVert 4) =
      Vcirc R (p.walk.getVert 6) ⊔ Z R (p.walk.getVert 6))
    (hV10 : hatV R (p.walk.getVert 10) (p.walk.getVert 12) =
      Vcirc R (p.walk.getVert 10) ⊔ Z R (p.walk.getVert 10))
    (hprod : (hatW R (p.walk.getVert 8) (p.walk.getVert 6) (p.walk.getVert 4) :
      Set (FreeAmalgam R)) * (Q R (p.walk.getVert 4) : Set (FreeAmalgam R)) =
      (Q R (p.walk.getVert 5) : Set (FreeAmalgam R))) :
    (hatW R (p.walk.getVert 8) (p.walk.getVert 10) (p.walk.getVert 12) :
      Set (FreeAmalgam R)) * (Q R (alpha R) : Set (FreeAmalgam R)) =
      (Q R (p.walk.getVert 5) : Set (FreeAmalgam R)) := by
  have he := Higher.OrbitGeometry.TwoCases.ZGeometry.NeighborAction.second_eq_backward_span
    hV6 hV10 (p.turns 8 (by decide) (by decide) (by decide))
  rw [he, hV6.trans hV6rev.symm]
  simpa only [hatW, p.center_eq] using hprod

/-- The source commutator at d descends through the common denominator with
index at most two. Orbit containment is precisely (4.5.4)(ii); the displayed
hat W commutator is the translated (4.5.3)(ii), not a higher quotient model. -/
theorem first_actor_bound [Finite M] {geometry : Geometry R}
    (earlier : Earlier R geometry) (p : Higher.SourcePath (alpha R))
    (horbit : NormalizerTransfer.conjugatesIn (Z R (p.walk.getVert 8))
      (stabilizer R (alpha R)) ≤ Q R (p.walk.getVert 8))
    (hcomm : ⁅hatW R (p.walk.getVert 8) (p.walk.getVert 10) (p.walk.getVert 12),
      Q R (p.walk.getVert 8)⁆ ≤ Z R (p.walk.getVert 8)) :
    (hatV R (alpha R) (p.walk.getVert 6)).relIndex
      ⁅orbitFactor p (p.walk.getVert 8),
        hatW R (p.walk.getVert 8) (p.walk.getVert 10) (p.walk.getVert 12)⁆ ≤ 2 := by
  have h7 : Adjacent R (p.walk.getVert 8) (p.walk.getVert 7) := by
    apply adjacent_symm
    exact (cosetGraph_adj R _ _).mp (SimpleGraph.dist_eq_one_iff_adj.mp
      (p.dist (i := 7) (j := 8) (by decide) (by decide)))
  have h6 : Adjacent R (p.walk.getVert 6) (p.walk.getVert 7) :=
    (cosetGraph_adj R _ _).mp (SimpleGraph.dist_eq_one_iff_adj.mp
      (p.dist (i := 6) (j := 7) (by decide) (by decide)))
  have hZ : Z R (p.walk.getVert 7) ≤ hatV R (alpha R) (p.walk.getVert 6) :=
    (Escape.EdgeTransfer.edge_Z_le _ _ (path_color p (by decide) (by decide)) h6).trans
      (PathCentrality.Z_le_localZSpan R _ _)
  have hC : ⁅orbitFactor p (p.walk.getVert 8),
      hatW R (p.walk.getVert 8) (p.walk.getVert 10) (p.walk.getVert 12)⁆ ≤
      Z R (p.walk.getVert 8) := by
    rw [commutator_comm]
    exact (commutator_mono le_rfl (first_factor_le_Q earlier p horbit)).trans hcomm
  let := finite_stabilizer R (p.walk.getVert 8)
  let : Finite (Z R (p.walk.getVert 8)) := Finite.of_injective
    (inclusion (Z_le_stabilizer R _)) (inclusion_injective _)
  have hb := (relIndex_le_of_le_right hC (by exact index_ne_zero_of_finite)).trans
    (relIndex_le_of_le_left hZ (by exact index_ne_zero_of_finite))
  exact hb.trans_eq (earlier.edge_Z_index _ _ (path_color p (by decide) (by decide)) h7)

/-- MS93 (4.5.4)(iii), the small actor and fixed dual-orientation test for
its first actual orbit quotient. The extra premises are only the literal
preceding (4.5.1)(iv), (4.5.3)(i--ii), and (4.5.4)(ii) conclusions. -/
theorem first_small_and_separated [Finite M] (source : LocalSource L R)
    {geometry : Geometry R} (common : CommonFacts R source geometry)
    (earlier : Earlier R geometry) (p : Higher.SourcePath (alpha R))
    (hV6 : hatV R (p.walk.getVert 6) (p.walk.getVert 8) =
      Vcirc R (p.walk.getVert 6) ⊔ Z R (p.walk.getVert 6))
    (hV6rev : hatV R (p.walk.getVert 6) (p.walk.getVert 4) =
      Vcirc R (p.walk.getVert 6) ⊔ Z R (p.walk.getVert 6))
    (hV10 : hatV R (p.walk.getVert 10) (p.walk.getVert 12) =
      Vcirc R (p.walk.getVert 10) ⊔ Z R (p.walk.getVert 10))
    (hprod : (hatW R (p.walk.getVert 8) (p.walk.getVert 6) (p.walk.getVert 4) :
      Set (FreeAmalgam R)) * (Q R (p.walk.getVert 4) : Set (FreeAmalgam R)) =
      (Q R (p.walk.getVert 5) : Set (FreeAmalgam R)))
    (horbit : NormalizerTransfer.conjugatesIn (Z R (p.walk.getVert 8))
      (stabilizer R (alpha R)) ≤ Q R (p.walk.getVert 8))
    (hcomm : ⁅hatW R (p.walk.getVert 8) (p.walk.getVert 10) (p.walk.getVert 12),
      Q R (p.walk.getVert 8)⁆ ≤ Z R (p.walk.getVert 8))
    (s : OrbitModule source p (p.walk.getVert 8)) : letI := s.normal
    Escape.Initial.Natural.Splitting.HasSmallInvolution s.action ∧
      DisplacementSeparation s.action common.natural.marking := by
  have ht : Adjacent R (alpha R) (p.walk.getVert 5) := by
    simpa only [p.center_eq] using (cosetGraph_adj R _ _).mp
      (SimpleGraph.dist_eq_one_iff_adj.mp
        (p.dist (i := 4) (j := 5) (by decide) (by decide)))
  exact small_and_separated_of_edge_product source common earlier s ht
    (first_actor_product p hV6 hV6rev hV10 hprod) (first_actor_bound earlier p horbit hcomm)


end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.CoreFactors.Higher.Quotients.SecondLayer.Recognition.Displacement
