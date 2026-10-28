module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.PathCentrality.FinalCalculation.Applications
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.EdgeTransfer
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.Propagation.Edges
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.Propagation.Backward.Control

/-!
# The final local-center and edge-index transfer in MS93 (4.4)

The symmetric moving-edge bound on printed p.895 supplies all the neighboring
B-containments required by the already proved (4.2)(i). That transfer puts
edge displacement in the actual Z-layer, hence every radius-generator
commutator in Z. Independently, the full natural section makes a genuine
moving orbit span contain Vcirc; (4.2)(iii) then gives residual fixation.
Together these prove centrality in the whole vertex stabilizer.

Order four at one actual edge transports to all oriented edges and gives
both source indices. The numerical application uses the literal alpha-2
vertex on the extended path to obtain |H_alpha| <= 4.

These results are conditional on the intermediate symmetric moving-edge
calculation, whose source proof remains required. They do not prove (4.4)
from the preceding source inputs alone. No contrary configuration from
(4.3) is used. Source: Meierfrankenfeld--Stellmacher (1993), p.895.
-/

public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
open scoped commutatorElement
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality.FinalCalculation.Conclusion
variable {M : Type*} [Group M] {L R : Subgroup M}
  {source : LocalSource L R} {geometry : Geometry R}

/-- The intermediate symmetric bound on p.895, with the literal moving set
and incident edge. This is a target, not a proved source input. -/
@[expose] def MovingEdgeFixed (geometry : Geometry R) : Prop :=
  ∀ c t d, color R c = false → Adjacent R c t → Adjacent R d t →
    d ∈ Escape.movingNeighbors geometry c → edgeCommutator R d t ≤ fixedCore R c

variable [Finite M]

/-- The moving edge bound and the nonmoving definition supply every
neighbor hypothesis of the actual (4.2)(i) transfer. -/
theorem neighbor_displacement_le_B (common : CommonFacts R source geometry)
    (hfixed : MovingEdgeFixed geometry) {c t d : Vertex R}
    (hc : color R c = false) (hct : Adjacent R c t) (hdt : Adjacent R d t) :
    edgeCommutator R d t ≤ B R c (geometry.Z_normal c) := by
  have hd : color R d = false := Escape.EdgeTransfer.neighbor_color c t d hc hct hdt
  by_cases hmove : d ∈ Escape.movingNeighbors geometry c
  · have hD := hfixed c t d hc hct hdt hmove
    have hV : edgeCommutator R d t ≤ V R c :=
      ((Escape.EdgeTransfer.edge_commutator_le_natural common.large_distance
        (LocalCommutator.moduleFacts common) d t hd hdt).trans (U_le_Z R d)).trans
          (le_iSup_of_le d (le_iSup_of_le (by rw [SimpleGraph.dist_comm, hmove.1]) le_rfl))
    intro x hx
    apply (mem_B_iff R c (geometry.Z_normal c)
      ((geometry.V_le_Q common.large_distance c hc).trans (fun _ hy => hy.1)) x).mpr
    refine ⟨hV hx, fun l hl => ?_⟩
    rw [commutatorElement_eq_one_iff_mul_comm.mpr ((hD hx).2 l hl)]
    exact (Z R c).one_mem
  · have hZ : Z R d ≤ B R c (geometry.Z_normal c) := by
      by_cases heq : c = d
      · subst d
        exact Escape.EdgeTransfer.Z_le_B common.large_distance c hc
      · have hdist := Escape.Propagation.neighbor_distance_two hc hct hdt heq
        exact of_not_not (fun hn => hmove ⟨hdist, hn⟩)
    exact ((Escape.EdgeTransfer.edge_commutator_le_natural common.large_distance
      (LocalCommutator.moduleFacts common) d t hd hdt).trans (U_le_Z R d)).trans hZ

/-- Apply the proved (4.2)(i), with no contrary configuration from (4.3). -/
theorem edge_le_Z (common : CommonFacts R source geometry)
    (hfixed : MovingEdgeFixed geometry) {c t : Vertex R}
    (hc : color R c = false) (hct : Adjacent R c t) :
    edgeCommutator R c t ≤ Z R t :=
  Escape.EdgeTransfer.edgeTransfer common.large_distance (LocalCommutator.moduleFacts common)
    c t hc hct (fun _d hd => neighbor_displacement_le_B common hfixed hc hct hd)

/-- All radius-two generators have their Q-displacement in the central
Z-layer once the neighboring edge calculation is available. -/
theorem radius_commutator_le_Z (common : CommonFacts R source geometry)
    (hfixed : MovingEdgeFixed geometry) {c : Vertex R} (hc : color R c = false) :
    ⁅V R c, Q R c⁆ ≤ Z R c := by
  have hgen (d : Vertex R) (hd : (cosetGraph R).dist d c ≤ 2) :
      ⁅Z R d, Q R c⁆ ≤ Z R c := by
    have hcases : (cosetGraph R).dist d c = 0 ∨
        (cosetGraph R).dist d c = 1 ∨ (cosetGraph R).dist d c = 2 := by omega
    rcases hcases with hzero | hone | htwo
    · have heq := (cosetGraph_connected R).dist_eq_zero_iff.mp hzero
      subst d
      rw [geometry.centralizes c hc]
      exact bot_le
    · have hcd := adjacent_symm R
        ((cosetGraph_adj R _ _).mp (SimpleGraph.dist_eq_one_iff_adj.mp hone))
      exact (commutator_mono (Escape.EdgeTransfer.edge_Z_le c d hc hcd) le_rfl).trans
        (by rw [geometry.centralizes c hc]; exact bot_le)
    · obtain ⟨t, hdt, hct⟩ := exists_common_neighbor_of_dist_two R d c htwo
      have ht : color R t = true := by
        have hn := adjacent_color_ne R hct
        cases h : color R t <;> simp_all
      have hdc := Escape.EdgeTransfer.neighbor_color c t d hc hct hdt
      exact (commutator_mono le_rfl (Q_le_adjacent_h R ht hct)).trans
        ((edge_le_Z common hfixed hdc hdt).trans (Escape.EdgeTransfer.edge_Z_le c t hc hct))
  have hle (d : Vertex R) : (⨆ (_ : (cosetGraph R).dist d c ≤ 2), Z R d) ≤ Q R c :=
    (le_iSup (fun d => ⨆ (_ : (cosetGraph R).dist d c ≤ 2), Z R d) d).trans
      (geometry.V_le_Q common.large_distance c hc)
  change ⁅⨆ d, ⨆ (_ : (cosetGraph R).dist d c ≤ 2), Z R d, Q R c⁆ ≤ Z R c
  rw [commutator_iSup_of_le _ _ hle]
  apply iSup_le
  intro d
  rw [commutator_iSup_of_le _ _ (fun hd =>
    (le_iSup (fun _ : (cosetGraph R).dist d c ≤ 2 => Z R d) hd).trans (hle d))]
  exact iSup_le fun hd => hgen d hd

/-- The full natural section makes one genuine moving span contain Vcirc.
Its fixed displacement then transfers to the whole radius by (4.2)(iii). -/
theorem radius_commutator_le_fixed (common : CommonFacts R source geometry)
    (hfixed : MovingEdgeFixed geometry) {c d : Vertex R} (hc : color R c = false)
    (s : Escape.NaturalSectionAt c (V R c) (Z R c))
    (hd : d ∈ Escape.movingNeighbors geometry c) :
    ⁅V R c, Q R c⁆ ≤ fixedCore R c := by
  obtain ⟨t, hct, hdt⟩ := exists_common_neighbor_of_dist_two R c d hd.1
  have ht : color R t = true := by
    have hn := adjacent_color_ne R hct
    cases h : color R t <;> simp_all
  have hcomm : ⁅Z R d, Q R c⁆ ≤ fixedCore R c :=
    (commutator_mono le_rfl (Q_le_adjacent_h R ht hct)).trans
      (hfixed c t d hc hct hdt hd)
  have hspan : Vcirc R c ≤ localZSpan R d c := by
    rw [localZSpan_eq_conjugates]
    exact Escape.Initial.Natural.moving_generation_of_naturalSection
      source geometry common.large_distance c hc s d hd
  apply common.normalization_transfer c hc (Q R c) le_rfl (Q_normal R c)
  exact (commutator_mono hspan le_rfl).trans
    ((LocalCommutator.span_commutator_le_fixed_iff hc
      (by rw [SimpleGraph.dist_comm, hd.1]) common.large_distance).mpr hcomm)

/-- The source fixed core centralizes the residual. The proved Z-bound
also centralizes Q, and these two groups generate the full stabilizer. -/
theorem local_centrality (common : CommonFacts R source geometry)
    (hfixed : MovingEdgeFixed geometry) {c d : Vertex R} (hc : color R c = false)
    (s : Escape.NaturalSectionAt c (V R c) (Z R c))
    (hd : d ∈ Escape.movingNeighbors geometry c) :
    ⁅V R c, Q R c⁆ ≤ (center (stabilizer R c)).map (stabilizer R c).subtype :=
  Escape.Propagation.Backward.le_localCenter_of_fixedCore source c hc _
    (radius_commutator_le_fixed common hfixed hc s hd)
    ((radius_commutator_le_Z common hfixed hc).trans
      (commutator_eq_bot_iff_le_centralizer.mp (geometry.centralizes c hc)))

/-- Genuine moving neighbors are transported from the retained extended path. -/
theorem exists_moving_neighbor (common : CommonFacts R source geometry)
    {a : Vertex R} (e : RegularPaths.ExtendedPath geometry a)
    {c : Vertex R} (hc : color R c = false) :
    ∃ d, d ∈ Escape.movingNeighbors geometry c := by
  obtain ⟨u, hu⟩ := exists_mVertex_of_color R (ExtendedPath.center_color e)
  obtain ⟨v, hv⟩ := exists_mVertex_of_color R hc
  let g := u⁻¹ * v
  have hg : act R g a = c := by rw [hu, act_mVertex, mul_inv_cancel_left, ← hv]
  refine ⟨act R g (e.walk.getVert 2), ?_⟩
  rw [← hg]
  exact (Escape.PairingControl.FirstPairing.movingNeighbors_act_iff
    common.large_distance g a (e.walk.getVert 2) (ExtendedPath.center_color e)).mpr
      (ExtendedPath.backward_moving e source common.large_distance)

/-- The conditional final local-centrality application at every M-vertex. -/
theorem centrality_at_all (common : CommonFacts R source geometry)
    (hfixed : MovingEdgeFixed geometry)
    (sections : ∀ c, color R c = false →
      Nonempty (Escape.NaturalSectionAt c (V R c) (Z R c)))
    {a : Vertex R} (e : RegularPaths.ExtendedPath geometry a)
    {c : Vertex R} (hc : color R c = false) :
    ⁅V R c, Q R c⁆ ≤ (center (stabilizer R c)).map (stabilizer R c).subtype := by
  obtain ⟨d, hd⟩ := exists_moving_neighbor common e hc
  obtain ⟨s⟩ := sections c hc
  exact local_centrality common hfixed hc s hd

omit [Finite M] in
/-- Displacement order is invariant under the actual oriented-edge action. -/
theorem edge_card_at_all {a t c u : Vertex R} (ha : color R a = false)
    (hc : color R c = false) (hat : Adjacent R a t) (hcu : Adjacent R c u)
    (hcard : Nat.card (edgeCommutator R a t) = 4) :
    Nat.card (edgeCommutator R c u) = 4 := by
  obtain ⟨g, hga, hgt⟩ := Escape.Propagation.exists_edge_transport ha hc hat hcu
  rw [← hga, ← hgt, RegularPaths.edgeCommutator_act,
    card_map_of_injective (MulAut.conj g⁻¹).injective, hcard]

/-- Both literal source indices, after the actual (4.2)(i) transfer.
Order four is the remaining product calculation, not an index premise. -/
theorem edge_indices (common : CommonFacts R source geometry)
    (hfixed : MovingEdgeFixed geometry) {a t c u : Vertex R}
    (ha : color R a = false) (hat : Adjacent R a t)
    (hcard : Nat.card (edgeCommutator R a t) = 4)
    (hc : color R c = false) (hcu : Adjacent R c u) :
    (Z R u).relIndex (Z R c) = 2 ∧ (Q R c).relIndex (Q R u) = 4 := by
  have hZ := edge_le_Z common hfixed hc hcu
  have hfour := edge_card_at_all ha hc hat hcu hcard
  exact ⟨Escape.Propagation.edge_Z_index_of_card common.large_distance
      (LocalCommutator.moduleFacts common) c u hc hcu hZ hfour,
    Escape.Propagation.edge_Q_index_of_card common.large_distance
      (LocalCommutator.moduleFacts common) c u hc hcu hZ hfour⟩

/-- The numerical consumer uses the actual alpha-2 moving neighbor and the
full preceding natural section. Centrality is supplied by the transfer above. -/
theorem H_card_le_four (common : CommonFacts R source geometry)
    (hfixed : MovingEdgeFixed geometry) {a : Vertex R}
    (e : RegularPaths.ExtendedPath geometry a)
    (s : Escape.NaturalSectionAt a (V R a) (Z R a)) : Nat.card (H R a) ≤ 4 := by
  have hmove := ExtendedPath.backward_moving e source common.large_distance
  have hspan : Vcirc R a ≤ localZSpan R (e.walk.getVert 2) a := by
    rw [localZSpan_eq_conjugates]
    exact Escape.Initial.Natural.moving_generation_of_naturalSection
      source geometry common.large_distance a (ExtendedPath.center_color e) s _ hmove
  exact Numerical.SourceCenterBound.DistanceGreaterFour.H_card_le_four_of_moving_span
    common (ExtendedPath.center_color e) (ExtendedPath.backward_distance e) hspan
    (local_centrality common hfixed (ExtendedPath.center_color e) s hmove)

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality.FinalCalculation.Conclusion
