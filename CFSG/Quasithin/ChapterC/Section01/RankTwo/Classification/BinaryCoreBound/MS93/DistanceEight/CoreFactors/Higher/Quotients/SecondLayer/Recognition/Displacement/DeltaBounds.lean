module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.CoreFactors.Higher.Quotients.SecondLayer.Recognition.Displacement.Transfer

/-!
# Delta's transported edge and quotient-displacement bound

The actual transporter fixes c and takes a to delta. It takes the edge
at index 5 to an edge incident with both delta and c. That edge's Z lies
in the common denominator and has index two in Z_delta. Together with
the radius bound on the denominator, this descends the literal local
(4.5.3)(ii) commutator bound to the actual delta orbit quotient.

The final theorem consumes an actual actor and its edge-kernel product.
Constructing that actor from delta's generation equation, with the source
hypotheses needed for the product, is still an obligation. No new regular
path, marking, faithfulness or movement premise is silently supplied here.
The orbit containment is the delta instance of (4.5.4)(ii), produced by
qt-c01-ms93-higher-orbit-geometry; a hat-W commutator is a translated
(4.5.3)(ii), produced by qt-c01-ms93-core-factors-early-layers.
Source: Meierfrankenfeld--Stellmacher (1993), (4.5.4)(iii), printed p.899.
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

/-- The actual transporter bounds delta's distance from the base vertex. -/
theorem delta_dist_base_le {p : Higher.SourcePath (alpha R)} (δ : DeltaChoice p) :
    (cosetGraph R).dist (alpha R) δ.vertex ≤ 4 := by
  have h := (cosetGraph_connected R).dist_triangle
    (u := alpha R) (v := p.walk.getVert 6) (w := δ.vertex)
  have hac : (cosetGraph R).dist (alpha R) (p.walk.getVert 6) = 2 := by
    simpa only [p.center_eq] using p.dist (i := 4) (j := 6) (by decide) (by decide)
  have hcd : (cosetGraph R).dist (p.walk.getVert 6) δ.vertex = 2 := by
    rw [SimpleGraph.dist_comm]
    exact delta_dist_middle δ
  rw [hac, hcd] at h
  exact h

/-- Delta's actual orbit containment and transporter put the enlarged factor
in Q_delta. The denominator is controlled by its radius, not by a new path. -/
theorem delta_factor_le_Q {geometry : Geometry R} (earlier : Earlier R geometry)
    {p : Higher.SourcePath (alpha R)} (δ : DeltaChoice p)
    (horbit : NormalizerTransfer.conjugatesIn (Z R δ.vertex)
      (stabilizer R (alpha R)) ≤ Q R δ.vertex) :
    orbitFactor p δ.vertex ≤ Q R δ.vertex := by
  refine sup_le horbit ?_
  exact (hatV_le_radius R p.two_step_distances.1.le).trans
    ((Escape.Propagation.RadiusFour.VBall_le_of_dist_add_le δ.vertex (alpha R) 2 6
      (by have := delta_dist_base_le δ; omega)).trans
      (Escape.Propagation.RadiusFour.VBall_le_Q δ.vertex (delta_color δ) 6
        (by rw [earlier.distance]; decide)))

/-- Delta's transported edge gives the exact index-two bound needed for
any actor satisfying the literal local (4.5.3)(ii) commutator inequality.
This uses delta's given transporter, and assumes no regular path at delta. -/
theorem delta_actor_bound [Finite M] {geometry : Geometry R}
    (earlier : Earlier R geometry) {p : Higher.SourcePath (alpha R)} (δ : DeltaChoice p)
    (horbit : NormalizerTransfer.conjugatesIn (Z R δ.vertex)
      (stabilizer R (alpha R)) ≤ Q R δ.vertex)
    {A : Subgroup (FreeAmalgam R)} (hcomm : ⁅A,Q R δ.vertex⁆ ≤ Z R δ.vertex) :
    (hatV R (alpha R) (p.walk.getVert 6)).relIndex ⁅orbitFactor p δ.vertex,A⁆ ≤ 2 := by
  let t := act R δ.transporter (p.walk.getVert 5)
  have ha5 : Adjacent R (alpha R) (p.walk.getVert 5) := by
    simpa only [p.center_eq] using (cosetGraph_adj R _ _).mp
      (SimpleGraph.dist_eq_one_iff_adj.mp
        (p.dist (i := 4) (j := 5) (by decide) (by decide)))
  have hc5 : Adjacent R (p.walk.getVert 6) (p.walk.getVert 5) := by
    apply adjacent_symm
    exact (cosetGraph_adj R _ _).mp (SimpleGraph.dist_eq_one_iff_adj.mp
      (p.dist (i := 5) (j := 6) (by decide) (by decide)))
  have hdt : Adjacent R δ.vertex t := by
    rw [δ.vertex_eq]
    exact (adjacent_act_iff R δ.transporter _ _).mpr ha5
  have hct : Adjacent R (p.walk.getVert 6) t := by
    have hh := (adjacent_act_iff R δ.transporter _ _).mpr hc5
    have hf : act R δ.transporter (p.walk.getVert 6) = p.walk.getVert 6 :=
      δ.transporter.property
    rwa [hf] at hh
  have hZ : Z R t ≤ hatV R (alpha R) (p.walk.getVert 6) :=
    (Escape.EdgeTransfer.edge_Z_le _ _ (path_color p (by decide) (by decide)) hct).trans
      (PathCentrality.Z_le_localZSpan R _ _)
  have hC : ⁅orbitFactor p δ.vertex,A⁆ ≤ Z R δ.vertex := by
    rw [commutator_comm]
    exact (commutator_mono le_rfl (delta_factor_le_Q earlier δ horbit)).trans hcomm
  let := finite_stabilizer R δ.vertex
  let : Finite (Z R δ.vertex) := Finite.of_injective
    (inclusion (Z_le_stabilizer R _)) (inclusion_injective _)
  have hb := (relIndex_le_of_le_right hC (by exact index_ne_zero_of_finite)).trans
    (relIndex_le_of_le_left hZ (by exact index_ne_zero_of_finite))
  exact hb.trans_eq (earlier.edge_Z_index _ _ (delta_color δ) hdt)

/-- The delta consumer for a justified local actor. Its edge product remains
an explicit geometric obligation; this is not the completed delta source result. -/
theorem delta_small_and_separated_of_actor [Finite M] (source : LocalSource L R)
    {geometry : Geometry R} (common : CommonFacts R source geometry)
    (earlier : Earlier R geometry) {p : Higher.SourcePath (alpha R)} (δ : DeltaChoice p)
    (s : OrbitModule source p δ.vertex) {t : Vertex R}
    (ht : Adjacent R (alpha R) t) {A : Subgroup (FreeAmalgam R)}
    (hprod : (A : Set (FreeAmalgam R)) * (Q R (alpha R) : Set (FreeAmalgam R)) =
      (Q R t : Set (FreeAmalgam R)))
    (horbit : NormalizerTransfer.conjugatesIn (Z R δ.vertex)
      (stabilizer R (alpha R)) ≤ Q R δ.vertex)
    (hcomm : ⁅A,Q R δ.vertex⁆ ≤ Z R δ.vertex) : letI := s.normal
    Escape.Initial.Natural.Splitting.HasSmallInvolution s.action ∧
      DisplacementSeparation s.action common.natural.marking :=
  small_and_separated_of_edge_product source common earlier s ht hprod
    (delta_actor_bound earlier δ horbit hcomm)

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.CoreFactors.Higher.Quotients.SecondLayer.Recognition.Displacement
