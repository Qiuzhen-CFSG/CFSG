module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.CoreFactors.Higher.OrbitGeometry.Replacement.Configuration
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.CoreFactors.Early.First.Intersections
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Early.EdgeStructure.IndexTwo
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.Propagation.Backward.Products.Selection.Pencil.Choices.FiniteGeometry.Planes

/-!
# The unequal-Z replacement: local actor and reverse-normalization obstruction

The selected neighbor has a different Z-layer from the original neighbor at
index seven: equality would identify their edge commutators, whereas Z_d
normalizes the original one and does not normalize the selected one.

For the actual binary natural action, the centralizer in G_c of an incident
Z-layer is its edge kernel. This follows from its order-four fixed plane and
the compatible local projection to SL₃(2). Consequently the bound
[Z_r,Z_c] ≤ H_d ≤ Z_(c+1) puts Z_r in N_(G_c)(Q_(c+1)), hence in the
printed product G_(c,c+1) C_c. The actor is the relative normalizer defined
on p.881, not the edge stabilizer. A reflected instance of (4.5.2)(i) then
makes Z_r normalize Z_d.

The selected edge layer is exactly Z_r ∩ Z_(d^g): it has index two in
Z_r, and criticality excludes Z_r ≤ Z_(d^g). Therefore Z_d cannot normalize
Z_r. Otherwise it would normalize this intersection and its natural edge
commutator, contradicting the replacement choice. This proves the precise
reverse-normalization obstruction for the actual selected endpoint.

The same normality also bounds [Z_r,Z_d] by the original forward edge
Z_(p[7]): the action on its index-two quotient in Z_d is trivial. Applying
the reverse-normalization obstruction then excludes Z_(p[7]) ≤ Z_r.

The radius-commutator equality is precisely (4.5.1)(i), and the final
normality premise is precisely the reflected (4.5.2)(i) at (d,c+1,c).
Both retain producer qt-c01-ms93-core-factors-early-layers; no complete
Early.OrbitFacts record is used. These are the local deductions on p.898.
The unequal-Z contradiction in the first sentence of p.899 remains unproved.
In particular, normalization of Z_d by Z_r cannot simply be reversed.
None of the exports asserts (4.5.4)(ii) or assumes that contradiction.

Source: Meierfrankenfeld--Stellmacher, Pushing up weak BN-pairs of rank two
(1993), notation p.881, (4.5.2)(i) p.897 and (4.5.4)(ii) pp.898--899.
-/

public section
open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.CoreFactors.Higher.OrbitGeometry.Replacement.Unequal
open PathCentrality PathCentrality.RegularPaths
open Escape.Propagation.Backward.Products.Selection.Choices
variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}
  {source : LocalSource L R} {geometry : Geometry R}

-- The fixed index two makes the action quadratic; evaluation computes its displacement.
private theorem edge_natural (common : CommonFacts R source geometry)
    (earlier : Earlier R geometry) {a t : Vertex R} (ha : color R a = false)
    (hat : Adjacent R a t) : edgeCommutator R a t = U R a ⊓ Z R t := by
  have hloc : Q R t ≤ stabilizer R a := fun _ hx => hx.2 a (adjacent_symm R hat)
  have hE : ⁅Z R a, Q R t⁆ ≤ Z R t :=
    commutator_le_of_normalized_index_two _ _ _
      (Escape.EdgeTransfer.edge_Z_le a t ha hat) (earlier.edge_Z_index a t ha hat)
      (hloc.trans (Z_normalized R a))
      ((show Q R t ≤ stabilizer R t from fun _ hx => hx.1).trans (Z_normalized R t))
  have hfixed := Escape.EdgeTransfer.edge_Z_eq_fixed common.large_distance (moduleFacts common) a t ha hat
  let := geometry.Z_elementary (lt_trans (by decide : 0 < 2) common.large_distance) a ha
  have hcard := DistanceFour.Early.actor_index_eq_displacement_card_of_fixed_index_two
    (Z R a) (Q R t) (hloc.trans (Z_normalized R a))
    (hE.trans (hfixed.le.trans inf_le_right))
    (by rw [← hfixed]; exact earlier.edge_Z_index a t ha hat)
  have hc : (centralizer (Z R a : Set (FreeAmalgam R))).relIndex (Q R t) = 4 := by
    rw [← inf_relIndex_right, inf_comm, common.centralizer a t ha hat]
    exact earlier.edge_Q_index a t ha hat
  exact (Escape.Propagation.edge_fixed_natural_eq_commutator common.large_distance
    (moduleFacts common) a t ha hat hE (hcard.symm.trans hc)).symm

omit [Finite M] in
private theorem endpoint_normalizes_first (common : CommonFacts R source geometry)
    {a a' : Vertex R} (p : CriticalPath R geometry a a') :
    Z R a' ≤ stabilizer R a ⊓
      normalizer (edgeCommutator R a (p.walk.getVert 1) : Set (FreeAmalgam R)) := by
  have hlocal := p.endpoint_Z_le_start_stabilizer (by have := common.large_distance; omega)
  have hQ : Z R a' ≤ Q R (p.walk.getVert 1) := by
    apply Z_le_Q_of_dist_lt R a' (geometry.exists_critical a' p.end_color)
    rw [SimpleGraph.dist_comm, p.dist_end, geometry.distance_constant a' p.end_color]
    change p.walk.length - 1 < geometry.b R
    have := p.length_eq_b
    have := common.large_distance
    omega
  exact le_inf hlocal (hQ.trans (normalizer_commutator_ge_right _ _))

private theorem edge_ne_of_nonnormalizing (common : CommonFacts R source geometry)
    (earlier : Earlier R geometry) {a a' t : Vertex R}
    (p : CriticalPath R geometry a a') (hat : Adjacent R a t)
    (hn : ¬ Z R a' ≤ stabilizer R a ⊓
      normalizer (edgeCommutator R a t : Set (FreeAmalgam R))) :
    Z R t ≠ Z R (p.walk.getVert 1) := by
  have hl := p.length_eq_b
  have hb := common.large_distance
  have hfirst : Adjacent R a (p.walk.getVert 1) := by
    simpa using (cosetGraph_adj R _ _).mp (p.walk.adj_getVert_succ (i := 0) (by omega))
  intro heq
  apply hn
  rw [edge_natural common earlier p.start_color hat, heq,
    ← edge_natural common earlier p.start_color hfirst]
  exact endpoint_normalizes_first common p


/-- The selected source neighbor has a different Z-layer from the original one. -/
theorem neighbor_Z_ne (common : CommonFacts R source geometry)
    (earlier : Earlier R geometry) {a : Vertex R} (p : Higher.SourcePath a)
    (g : stabilizer R a)
    (hd : (cosetGraph R).dist (act R g (p.walk.getVert 8)) (p.walk.getVert 8) = 8)
    (hn : ¬ Z R (act R g (p.walk.getVert 8)) ≤ Q R (p.walk.getVert 8))
    (w : Witness p g) :
    Z R w.neighbor ≠ Z R (act R g (p.walk.getVert 7)) :=
  edge_ne_of_nonnormalizing common earlier (orbitCriticalPath p earlier g hd hn)
    w.first_adjacent w.nonnormalization

private theorem edge_plane_card (common : CommonFacts R source geometry)
    (earlier : Earlier R geometry) {a t : Vertex R} (ha : color R a = false)
    (hat : Adjacent R a t) : Nat.card (U R a ⊓ Z R t : Subgroup (FreeAmalgam R)) = 4 := by
  have hi := (Escape.Propagation.edge_Z_index_eq_natural common.large_distance
    (moduleFacts common) a t ha hat).symm.trans (earlier.edge_Z_index a t ha hat)
  have hcard := Subgroup.card_mul_index ((Z R t).subgroupOf (U R a))
  have he : (Z R t).subgroupOf (U R a) =
      (U R a ⊓ Z R t).subgroupOf (U R a) := by simp only [inf_subgroupOf_left]
  have hn : Nat.card ((Z R t).subgroupOf (U R a)) =
      Nat.card (U R a ⊓ Z R t : Subgroup (FreeAmalgam R)) := by
    rw [he]
    exact Nat.card_congr (subgroupOfEquivOfLe inf_le_left).toEquiv
  change Nat.card ((Z R t).subgroupOf (U R a)) * (Z R t).relIndex (U R a) = _ at hcard
  rw [hn, hi, common.natural.card_at a ha] at hcard
  omega

private theorem edge_actor_image (common : CommonFacts R source geometry)
    (earlier : Earlier R geometry) {a t : Vertex R} (ha : color R a = false)
    (hat : Adjacent R a t) (model : LocalModel a) :
    model.actorImage (Q R t) = planeFixer (model.coordinates (U R a ⊓ Z R t)) := by
  have hloc : Q R t ≤ stabilizer R a := fun _ hx => hx.2 a (adjacent_symm R hat)
  have hfix : U R a ⊓ Z R t ≤ centralizer (Q R t : Set (FreeAmalgam R)) := by
    rw [Escape.EdgeTransfer.edge_Z_eq_fixed common.large_distance (moduleFacts common) a t ha hat]
    exact inf_le_right.trans inf_le_right
  apply eq_of_le_of_card_ge
  · rintro _ ⟨g, hg, rfl⟩ _ ⟨u, hu, rfl⟩
    exact (model.action_fixed_iff g u).mpr (hfix hu g hg)
  · rw [model.actorImage_card _ hloc, earlier.edge_Q_index a t ha hat,
      FiniteGeometry.planeFixer_card _ (by
        rw [model.coordinates_card _ inf_le_left, edge_plane_card common earlier ha hat])]

/-- In the binary natural action the whole local centralizer of the incident
Z-layer is the actual edge kernel. -/
theorem edge_Z_centralizer (common : CommonFacts R source geometry)
    (earlier : Earlier R geometry) {a t : Vertex R} (ha : color R a = false)
    (hat : Adjacent R a t) :
    stabilizer R a ⊓ centralizer (Z R t : Set (FreeAmalgam R)) = Q R t := by
  obtain ⟨model⟩ := localModel_nonempty source (moduleFacts common) a ha
  have ht : color R t = true := by
    have hn := adjacent_color_ne R hat
    cases hc : color R t <;> simp_all
  have hpre := model.actorImage_comap (Q R t) (Q_le_adjacent_h R ht hat)
  rw [edge_actor_image common earlier ha hat model] at hpre
  apply le_antisymm
  · intro x hx
    let g : stabilizer R a := ⟨x, hx.1⟩
    have hg : g ∈ (planeFixer (model.coordinates (U R a ⊓ Z R t))).comap
        model.projection := by
      rintro _ ⟨u, hu, rfl⟩
      exact (model.action_fixed_iff g u).mpr (hx.2 u hu.2).symm
    rw [hpre] at hg
    exact hg
  · refine le_inf (fun _ hx => hx.2 a (adjacent_symm R hat)) ?_
    rw [Escape.EdgeTransfer.edge_Z_eq_fixed common.large_distance (moduleFacts common) a t ha hat]
    exact le_centralizer_iff.mp inf_le_right

/-- Normalizing an incident Z-layer normalizes its actual edge kernel.
The local group in the conclusion is the relative normalizer from p.881. -/
theorem edge_Z_normalizer_le (common : CommonFacts R source geometry)
    (earlier : Earlier R geometry) {a t : Vertex R} (ha : color R a = false)
    (hat : Adjacent R a t) :
    stabilizer R a ⊓ normalizer (Z R t : Set (FreeAmalgam R)) ≤
      stabilizer R a ⊓ normalizer (Q R t : Set (FreeAmalgam R)) := by
  apply le_inf inf_le_left
  rw [← edge_Z_centralizer common earlier ha hat]
  exact (le_inf (inf_le_left.trans (stabilizer R a).le_normalizer)
    (inf_le_right.trans (normalizer_le_normalizer_centralizer (Z R t)))).trans
      inf_normalizer_le_normalizer_inf

/-- The last local deduction on p.898, with the actual selected endpoint.
Its sole extra premise is the literal preceding (4.5.1)(i). In the binary
case the bound already holds in the relative normalizer before adjoining C_c. -/
theorem endpoint_le_relativeNormalizer (common : CommonFacts R source geometry)
    (earlier : Earlier R geometry) {a : Vertex R} (p : Higher.SourcePath a)
    {g : stabilizer R a} (w : Witness p g)
    (hcomm : ⁅V R a, V R (p.walk.getVert 8)⁆ = H R a ⊓ H R (p.walk.getVert 8)) :
    Z R w.endpoint ≤ stabilizer R (p.walk.getVert 6) ⊓
      normalizer (Q R (p.walk.getVert 7) : Set (FreeAmalgam R)) := by
  have hc := (walk_vertex_color p.start_color p.walk
    (by rw [p.length_eq]; decide)).mpr (by decide : Even 6)
  have hd := (walk_vertex_color p.start_color p.walk
    (by rw [p.length_eq]; decide)).mpr (by decide : Even 8)
  have hct : Adjacent R (p.walk.getVert 6) (p.walk.getVert 7) :=
    (cosetGraph_adj R _ _).mp (p.walk.adj_getVert_succ (by rw [p.length_eq]; decide))
  have hdt : Adjacent R (p.walk.getVert 8) (p.walk.getVert 7) :=
    adjacent_symm R ((cosetGraph_adj R _ _).mp
      (p.walk.adj_getVert_succ (i := 7) (by rw [p.length_eq]; decide)))
  have hcrit : CriticalPair R w.endpoint (p.walk.getVert 6)
      (geometry.exists_critical _ w.endpoint_color) := by
    refine ⟨?_, w.critical_noncontainment⟩
    rw [geometry.distance_constant _ w.endpoint_color]
    exact w.critical_distance.trans earlier.distance.symm
  have hloc := (source.critical_Z_le_stabilizer geometry _ w.endpoint_color _ hcrit).1
  have hbound := (w.commutator_le_H earlier hcomm).trans
    (Early.H_le_edge_Z common earlier hd hdt)
  have hn : Z R w.endpoint ≤ normalizer (Z R (p.walk.getVert 7) : Set (FreeAmalgam R)) := by
    apply le_normalizer_iff_commutator_le_right.mpr
    exact (commutator_mono le_rfl (Escape.EdgeTransfer.edge_Z_le _ _ hc hct)).trans hbound
  exact (le_inf hloc hn).trans (edge_Z_normalizer_le common earlier hc hct)

open scoped Pointwise in
/-- The printed actor bound, retaining the literal setwise product with C_c. -/
theorem endpoint_le_source_actor (common : CommonFacts R source geometry)
    (earlier : Earlier R geometry) {a : Vertex R} (p : Higher.SourcePath a)
    {g : stabilizer R a} (w : Witness p g)
    (hcomm : ⁅V R a, V R (p.walk.getVert 8)⁆ = H R a ⊓ H R (p.walk.getVert 8)) :
    (Z R w.endpoint : Set (FreeAmalgam R)) ⊆
      ((stabilizer R (p.walk.getVert 6) ⊓
        normalizer (Q R (p.walk.getVert 7) : Set (FreeAmalgam R)) :
          Subgroup (FreeAmalgam R)) : Set (FreeAmalgam R)) *
        (C R (p.walk.getVert 6) : Set (FreeAmalgam R)) := by
  intro x hx
  exact ⟨x, endpoint_le_relativeNormalizer common earlier p w hcomm hx,
    1, (C R (p.walk.getVert 6)).one_mem, mul_one x⟩

/-- Apply the reflected instance of (4.5.2)(i): Z_d is normal in
N_(G_c)(Q_(c+1)). The early-layer owner must supply that literal normality.
This gives normalization of Z_d by Z_r, not yet the unequal-Z contradiction. -/
theorem endpoint_normalizes_forward_Z (common : CommonFacts R source geometry)
    (earlier : Earlier R geometry) {a : Vertex R} (p : Higher.SourcePath a)
    {g : stabilizer R a} (w : Witness p g)
    (hcomm : ⁅V R a, V R (p.walk.getVert 8)⁆ = H R a ⊓ H R (p.walk.getVert 8))
    (hnormal : ((Z R (p.walk.getVert 8)).subgroupOf
      (stabilizer R (p.walk.getVert 6) ⊓
        normalizer (Q R (p.walk.getVert 7) : Set (FreeAmalgam R)))).Normal) :
    Z R w.endpoint ≤ normalizer (Z R (p.walk.getVert 8) : Set (FreeAmalgam R)) := by
  have hc := (walk_vertex_color p.start_color p.walk
    (by rw [p.length_eq]; decide)).mpr (by decide : Even 6)
  have hct : Adjacent R (p.walk.getVert 6) (p.walk.getVert 7) :=
    (cosetGraph_adj R _ _).mp (p.walk.adj_getVert_succ (by rw [p.length_eq]; decide))
  have hZQ : Z R (p.walk.getVert 8) ≤ Q R (p.walk.getVert 6) :=
    (le_iSup_of_le _ (le_iSup_of_le p.two_step_distances.2.1.le le_rfl) :
      Z R (p.walk.getVert 8) ≤ V R (p.walk.getVert 6)).trans
        (V_le_Q R hc common.large_distance)
  have hinc := hZQ.trans (LocalModel.kernel_le_relativeNormalizer _ hc hct)
  exact (endpoint_le_relativeNormalizer common earlier p w hcomm).trans
    ((normal_subgroupOf_iff_le_normalizer hinc).mp hnormal)

private theorem inf_eq_of_index_two {G : Type*} [Group G] {A B E : Subgroup G}
    (hEA : E ≤ A) (hEB : E ≤ B) (hi : E.relIndex A = 2) (hn : ¬ A ≤ B) :
    A ⊓ B = E := by
  have hEI : E ≤ A ⊓ B := le_inf hEA hEB
  have hiI := relIndex_mul_relIndex E (A ⊓ B) A hEI inf_le_left
  rw [hi] at hiI
  have hdiv : (A ⊓ B).relIndex A ∣ 2 :=
    ⟨E.relIndex (A ⊓ B), by rw [mul_comm]; exact hiI.symm⟩
  have htwo : (A ⊓ B).relIndex A = 2 := by
    rcases Nat.prime_two.eq_one_or_self_of_dvd _ hdiv with h | h
    · exact (hn ((relIndex_eq_one.mp h).trans inf_le_right)).elim
    · exact h
  rw [htwo] at hiI
  exact le_antisymm (relIndex_eq_one.mp (by omega)) hEI

omit [Finite M] in
/-- The selected edge layer is the exact intersection of its two even endpoints.
Criticality excludes equality of their whole Z-layers; edge index two then
leaves precisely the common incident Z-layer. -/
theorem endpoint_inf_pivot_Z (earlier : Earlier R geometry)
    {a : Vertex R} (p : Higher.SourcePath a) (g : stabilizer R a)
    (hd : (cosetGraph R).dist (act R g (p.walk.getVert 8)) (p.walk.getVert 8) = 8)
    (hn : ¬ Z R (act R g (p.walk.getVert 8)) ≤ Q R (p.walk.getVert 8))
    (w : Witness p g) :
    Z R w.endpoint ⊓ Z R (act R g (p.walk.getVert 8)) = Z R w.neighbor := by
  let q := orbitCriticalPath p earlier g hd hn
  have hpivotQ : Z R (act R g (p.walk.getVert 8)) ≤ Q R (p.walk.getVert 6) := by
    apply Z_le_Q_of_dist_lt R _ (geometry.exists_critical _ q.start_color)
    have hdist := q.dist_start (i := 6) (by change 6 ≤ 8; decide)
    change (cosetGraph R).dist (act R g (p.walk.getVert 8)) (p.walk.getVert 6) = 6 at hdist
    rw [hdist, geometry.distance_constant _ q.start_color]
    change 6 < geometry.b R
    rw [earlier.distance]
    decide
  exact inf_eq_of_index_two
    (Escape.EdgeTransfer.edge_Z_le _ _ w.endpoint_color w.second_adjacent)
    (Escape.EdgeTransfer.edge_Z_le _ _ q.start_color w.first_adjacent)
    (earlier.edge_Z_index _ _ w.endpoint_color w.second_adjacent)
    (fun h => w.critical_noncontainment (h.trans hpivotQ))

/-- Reverse normalization is impossible for the actual selected endpoint.
It would normalize the selected incident Z-layer, and hence its natural
edge commutator, contrary to the defining replacement choice. This is the
opposite direction from `endpoint_normalizes_forward_Z`. -/
theorem forward_Z_not_normalizes_endpoint (common : CommonFacts R source geometry)
    (earlier : Earlier R geometry) {a : Vertex R} (p : Higher.SourcePath a)
    (g : stabilizer R a)
    (hd : (cosetGraph R).dist (act R g (p.walk.getVert 8)) (p.walk.getVert 8) = 8)
    (hn : ¬ Z R (act R g (p.walk.getVert 8)) ≤ Q R (p.walk.getVert 8))
    (w : Witness p g) :
    ¬ Z R (p.walk.getVert 8) ≤ normalizer (Z R w.endpoint : Set (FreeAmalgam R)) := by
  intro hnorm
  let q := orbitCriticalPath p earlier g hd hn
  have hlocal := (source.critical_Z_le_stabilizer geometry _ q.start_color _ q.critical).2
  have hnZ : Z R (p.walk.getVert 8) ≤ normalizer (Z R w.neighbor : Set (FreeAmalgam R)) := by
    rw [← endpoint_inf_pivot_Z earlier p g hd hn w]
    exact (le_inf hnorm (hlocal.trans (Z_normalized R _))).trans
      inf_normalizer_le_normalizer_inf
  apply w.nonnormalization
  refine le_inf hlocal ?_
  rw [edge_natural common earlier q.start_color w.first_adjacent]
  exact (le_inf (hlocal.trans (U_normalized _)) hnZ).trans
    inf_normalizer_le_normalizer_inf

/-- The literal normality in (4.5.2)(i) gives a sharper displacement bound.
The selected endpoint normalizes both Z_d and its index-two edge layer Z_t;
it therefore acts trivially on Z_d/Z_t. This is a bound on the actual
replacement commutator, not a reversal of the normalization relation. -/
theorem endpoint_forward_commutator_le_edge (common : CommonFacts R source geometry)
    (earlier : Earlier R geometry) {a : Vertex R} (p : Higher.SourcePath a)
    {g : stabilizer R a} (w : Witness p g)
    (hcomm : ⁅V R a, V R (p.walk.getVert 8)⁆ = H R a ⊓ H R (p.walk.getVert 8))
    (hnormal : ((Z R (p.walk.getVert 8)).subgroupOf
      (stabilizer R (p.walk.getVert 6) ⊓
        normalizer (Q R (p.walk.getVert 7) : Set (FreeAmalgam R)))).Normal) :
    ⁅Z R w.endpoint, Z R (p.walk.getVert 8)⁆ ≤ Z R (p.walk.getVert 7) := by
  have hc := (walk_vertex_color p.start_color p.walk
    (by rw [p.length_eq]; decide)).mpr (by decide : Even 6)
  have hd := (walk_vertex_color p.start_color p.walk
    (by rw [p.length_eq]; decide)).mpr (by decide : Even 8)
  have hct : Adjacent R (p.walk.getVert 6) (p.walk.getVert 7) :=
    (cosetGraph_adj R _ _).mp (p.walk.adj_getVert_succ (by rw [p.length_eq]; decide))
  have hdt : Adjacent R (p.walk.getVert 8) (p.walk.getVert 7) :=
    adjacent_symm R ((cosetGraph_adj R _ _).mp
      (p.walk.adj_getVert_succ (i := 7) (by rw [p.length_eq]; decide)))
  have hnedge : Z R w.endpoint ≤
      normalizer (Z R (p.walk.getVert 7) : Set (FreeAmalgam R)) := by
    apply le_normalizer_iff_commutator_le_right.mpr
    exact (commutator_mono le_rfl (Escape.EdgeTransfer.edge_Z_le _ _ hc hct)).trans
      ((w.commutator_le_H earlier hcomm).trans (Early.H_le_edge_Z common earlier hd hdt))
  rw [commutator_comm]
  exact commutator_le_of_normalized_index_two _ _ _
    (Escape.EdgeTransfer.edge_Z_le _ _ hd hdt)
    (earlier.edge_Z_index _ _ hd hdt)
    (endpoint_normalizes_forward_Z common earlier p w hcomm hnormal) hnedge

/-- Actual application of the displacement bound to the replacement obstruction:
the original forward edge layer cannot lie in the selected endpoint's Z-layer.
Such containment would reverse the normalization and contradict the prescribed
nonnormalizing edge. The unequal-beta source inference is still needed. -/
theorem forward_edge_Z_not_le_endpoint (common : CommonFacts R source geometry)
    (earlier : Earlier R geometry) {a : Vertex R} (p : Higher.SourcePath a)
    (g : stabilizer R a)
    (hd : (cosetGraph R).dist (act R g (p.walk.getVert 8)) (p.walk.getVert 8) = 8)
    (hn : ¬ Z R (act R g (p.walk.getVert 8)) ≤ Q R (p.walk.getVert 8))
    (w : Witness p g)
    (hcomm : ⁅V R a, V R (p.walk.getVert 8)⁆ = H R a ⊓ H R (p.walk.getVert 8))
    (hnormal : ((Z R (p.walk.getVert 8)).subgroupOf
      (stabilizer R (p.walk.getVert 6) ⊓
        normalizer (Q R (p.walk.getVert 7) : Set (FreeAmalgam R)))).Normal) :
    ¬ Z R (p.walk.getVert 7) ≤ Z R w.endpoint := by
  intro h
  apply forward_Z_not_normalizes_endpoint common earlier p g hd hn w
  apply le_normalizer_iff_commutator_le_left.mpr
  exact (endpoint_forward_commutator_le_edge common earlier p w hcomm hnormal).trans h

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.CoreFactors.Higher.OrbitGeometry.Replacement.Unequal
