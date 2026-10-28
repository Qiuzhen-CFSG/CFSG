module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.PathCentrality.FinalCalculation.Conclusion.Distance
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.Initial.Bounds
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.Initial.Consequences.Geometry
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.Propagation.RadiusFour.Ball


/-!
# The symmetric moving-edge calculation in MS93 (4.4)

Put d = alpha'-4, c = alpha'-6, and A = V_alpha^(4). Distances on the
retained extended path put A in Q_c and make A centralize the radius at
alpha'-7. The decomposition V_c = Vcirc_c V_(alpha'-7) therefore puts the
literal product K = [Z_d,A] in H_c. Its order four identifies it with
[Z_d,Q_c], whose order is at most four. The product's fixed-core bound and
the full natural section then put [V_c,Q_c] in D_c.

Transport gives this fixation and |H_c| >= 4 at every M-vertex. For any
moving neighbor d of c, natural-section generation puts H_c in the local
normal closure of [Z_d,Q_c]. Fixation makes that displacement relatively
normal: the residual centralizes it and Q_c normalizes it. Thus H_c lies
in the displacement itself. The order-at-most-four incident edge contains
it, forcing edge(d,t) = H_c <= D_c. This is the symmetric moving-edge bound;
the existing transfer then supplies actual local centrality.

The explicit ProductCalculation premise is produced by the independent
selected-product task qt-c01-ms93-conclusion-selected-product. Final source
assembly and its discharge remain with qt-c01-ms93-final-calculation-conclusion.
One product on the retained path suffices. The natural sections retain their
literal quotient action, and all normality is relative to the specified
stabilizer. No distance-eight, local-centrality or final-index premise is used.

Source: Meierfrankenfeld--Stellmacher, Pushing up weak BN-pairs of rank two
(1993), original (4.4), printed p.895, the paragraph following (4.4.5).
-/

public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality.FinalCalculation.Conclusion.SymmetricSource
variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}
  {source : LocalSource L R} {geometry : Geometry R}

/-- The natural section extends fixation of one moving displacement to the radius. -/
theorem radius_fixed_of_moving (common : CommonFacts R source geometry)
    {c d : Vertex R} (hc : color R c = false)
    (s : Escape.NaturalSectionAt c (V R c) (Z R c))
    (hd : d ∈ Escape.movingNeighbors geometry c)
    (hfixed : ⁅Z R d, Q R c⁆ ≤ fixedCore R c) :
    ⁅V R c, Q R c⁆ ≤ fixedCore R c := by
  have hspan : Vcirc R c ≤ localZSpan R d c := by
    rw [localZSpan_eq_conjugates]
    exact Escape.Initial.Natural.moving_generation_of_naturalSection
      source geometry common.large_distance c hc s d hd
  apply common.normalization_transfer c hc (Q R c) le_rfl (Q_normal R c)
  exact (commutator_mono hspan le_rfl).trans
    ((LocalCommutator.span_commutator_le_fixed_iff hc
      (by rw [SimpleGraph.dist_comm, hd.1]) common.large_distance).mpr hfixed)

/-- Residual fixation and kernel normalization make the moving displacement
relatively normal. Natural-section generation therefore puts H inside it. -/
theorem H_le_moving_displacement (common : CommonFacts R source geometry)
    {c d : Vertex R} (hc : color R c = false)
    (s : Escape.NaturalSectionAt c (V R c) (Z R c))
    (hd : d ∈ Escape.movingNeighbors geometry c)
    (hfixed : ⁅Z R d, Q R c⁆ ≤ fixedCore R c) :
    H R c ≤ ⁅Z R d, Q R c⁆ := by
  have hspan : Vcirc R c ≤ localZSpan R d c := by
    rw [localZSpan_eq_conjugates]
    exact Escape.Initial.Natural.moving_generation_of_naturalSection
      source geometry common.large_distance c hc s d hd
  have hn : stabilizer R c ≤ normalizer (⁅Z R d, Q R c⁆ : Subgroup (FreeAmalgam R)) := by
    rw [← source.local_generation c hc]
    exact sup_le
      ((le_centralizer_iff.mp (hfixed.trans inf_le_right)).trans
        (Subgroup.centralizer_le_normalizer _))
      (normalizer_commutator_ge_right _ _)
  apply (commutator_mono hspan le_rfl).trans
  rw [LocalCommutator.span_commutator_eq_conjugates hc
    (by rw [SimpleGraph.dist_comm, hd.1]) common.large_distance]
  apply iSup_le
  intro g
  exact (mem_normalizer_iff_map_conj_eq.mp (hn ((stabilizer R c).inv_mem g.property))).le

/-- The preceding edge radius centralizes the actor, so the actor displaces
every radius generator into H. Both groups are inside the actual kernel. -/
theorem displacement_le_H (common : CommonFacts R source geometry)
    {c d t : Vertex R} (hc : color R c = false)
    (hct : Adjacent R c t) (hd : (cosetGraph R).dist d c ≤ 2)
    {A : Subgroup (FreeAmalgam R)} (hA : A ≤ Q R c)
    (hcentral : ⁅V R t, A⁆ = ⊥) : ⁅Z R d, A⁆ ≤ H R c := by
  have hVQ := geometry.V_le_Q common.large_distance c hc
  have hVW : V R c ≤ commutatorPreimage (Q R c) A (H R c) := by
    rw [Escape.Initial.Consequences.radius_eq_moving_sup_edge source hc hct]
    exact sup_le
      (le_commutatorPreimage ((Escape.Initial.Consequences.Vcirc_le_V c).trans hVQ)
        (commutator_mono le_rfl hA))
      (le_commutatorPreimage
        ((Escape.Initial.Consequences.edge_radius_le_radius hc hct).trans hVQ)
        (hcentral.le.trans bot_le))
  have hZV : Z R d ≤ V R c := le_iSup_of_le d (le_iSup_of_le hd le_rfl)
  exact (commutator_mono (hZV.trans hVW) le_rfl).trans
    (commutator_commutatorPreimage_le _ _ _ (normalizer_commutator_ge_right _ _))

omit [Finite M] in
/-- The literal radius-four actor lies in the kernel at alpha'-6. -/
theorem actor_le_kernel (hb : 6 < geometry.b R)
    {a : Vertex R} (e : RegularPaths.ExtendedPath geometry a) :
    VBall R a 4 ≤ Q R (e.walk.getVert (geometry.b R - 2)) := by
  have heven : Even (geometry.b R - 2) := by
    have he := geometry.even (alpha R) rfl
    change Even (geometry.b R) at he
    rw [Nat.even_iff] at he ⊢
    omega
  have hc := ExtendedPath.vertex_color e heven (by omega)
  apply (Escape.Propagation.RadiusFour.VBall_le_of_dist_add_le
    (e.walk.getVert (geometry.b R - 2)) a 4 (geometry.b R - 2) ?_).trans
    (Escape.Propagation.RadiusFour.VBall_le_Q _ hc _ (by omega))
  have hd := ExtendedPath.distance e (i := 4) (j := geometry.b R - 2)
    (by omega) (by omega)
  rw [e.center_eq] at hd
  rw [hd]
  omega

omit [Finite M] in
/-- Distances make the preceding edge radius centralize the radius-four actor. -/
theorem preceding_radius_centralizes_actor (hb : 6 < geometry.b R)
    {a : Vertex R} (e : RegularPaths.ExtendedPath geometry a) :
    ⁅V R (e.walk.getVert (geometry.b R - 3)), VBall R a 4⁆ = ⊥ := by
  have heven : Even (geometry.b R - 2) := by
    have he := geometry.even (alpha R) rfl
    change Even (geometry.b R) at he
    rw [Nat.even_iff] at he ⊢
    omega
  have hc := ExtendedPath.vertex_color e heven (by omega)
  have hct : Adjacent R (e.walk.getVert (geometry.b R - 2))
      (e.walk.getVert (geometry.b R - 3)) := by
    have hh := adjacent_symm R (path_adjacent e (geometry.b R - 3) (by omega))
    rwa [show geometry.b R - 3 + 1 = geometry.b R - 2 by omega] at hh
  have hat : (cosetGraph R).dist a (e.walk.getVert (geometry.b R - 3)) =
      geometry.b R - 7 := by
    have hh := ExtendedPath.distance e (i := 4) (j := geometry.b R - 3)
      (by omega) (by omega)
    rw [e.center_eq] at hh
    exact hh.trans (by omega)
  apply commutator_eq_bot_iff_le_centralizer.mpr
  apply Escape.Initial.Consequences.V_le_of_h_neighbors hc hct
  intro x hxt
  have hx : color R x = false :=
    Escape.EdgeTransfer.neighbor_color _ _ _ hc hct hxt
  have hdist : (cosetGraph R).dist a x ≤ geometry.b R - 6 := by
    have htx := SimpleGraph.dist_eq_one_iff_adj.mpr
      ((cosetGraph_adj R _ _).mpr (adjacent_symm R hxt))
    have htri := (cosetGraph_connected R).dist_triangle
      (u := a) (v := e.walk.getVert (geometry.b R - 3)) (w := x)
    omega
  have hAQ : VBall R a 4 ≤ Q R x :=
    (Escape.Propagation.RadiusFour.VBall_le_of_dist_add_le x a 4
      (geometry.b R - 2) (by omega)).trans
      (Escape.Propagation.RadiusFour.VBall_le_Q x hx _ (by omega))
  exact (commutator_eq_bot_iff_le_centralizer.mp (geometry.centralizes x hx)).trans
    (centralizer_le hAQ)

/-- The first critical window certifies genuine movement at alpha'-6. -/
theorem opposite_moving (common : CommonFacts R source geometry)
    (hb : 6 < geometry.b R) {a : Vertex R} (e : RegularPaths.ExtendedPath geometry a) :
    e.walk.getVert (geometry.b R) ∈
      Escape.movingNeighbors geometry (e.walk.getVert (geometry.b R - 2)) := by
  let p := e.window 0 (by decide) (by decide)
  have hp : CriticalPair R (e.walk.getVert 0) (e.walk.getVert (geometry.b R))
      (geometry.exists_critical _ p.start_color) := by simpa only [Nat.zero_add] using p.critical
  apply Escape.Propagation.RadiusFour.Forward.Reversal.critical_endpoint_moving
    source common.large_distance p.start_color hp
  constructor
  · rw [ExtendedPath.distance e (by omega) (by omega)]
    omega
  · rw [ExtendedPath.distance e (by omega) (by omega),
      ExtendedPath.distance e (i := 0) (j := geometry.b R) (by omega) (by omega)]
    omega

/-- The literal product lies in H at alpha'-6 by radius decomposition. -/
theorem product_le_H (common : CommonFacts R source geometry)
    (hb : 6 < geometry.b R) {a : Vertex R} (e : RegularPaths.ExtendedPath geometry a) :
    terminalProduct e ≤ H R (e.walk.getVert (geometry.b R - 2)) := by
  have heven : Even (geometry.b R - 2) := by
    have he := geometry.even (alpha R) rfl
    change Even (geometry.b R) at he
    rw [Nat.even_iff] at he ⊢
    omega
  apply displacement_le_H common (ExtendedPath.vertex_color e heven (by omega))
    (t := e.walk.getVert (geometry.b R - 3))
  · have hh := adjacent_symm R (path_adjacent e (geometry.b R - 3) (by omega))
    rwa [show geometry.b R - 3 + 1 = geometry.b R - 2 by omega] at hh
  · rw [SimpleGraph.dist_comm, ExtendedPath.distance e (by omega) (by omega)]
    omega
  · exact actor_le_kernel hb e
  · exact preceding_radius_centralizes_actor hb e

/-- Order four identifies the literal product with displacement toward the center. -/
theorem product_eq_displacement (common : CommonFacts R source geometry)
    (hb : 6 < geometry.b R) {a : Vertex R} (e : RegularPaths.ExtendedPath geometry a)
    (product : ProductCalculation e) :
    terminalProduct e = ⁅Z R (e.walk.getVert (geometry.b R)),
      Q R (e.walk.getVert (geometry.b R - 2))⁆ := by
  have hd := ExtendedPath.vertex_color e (i := geometry.b R)
    (geometry.even (alpha R) rfl) (by omega)
  have hdist : (cosetGraph R).dist (e.walk.getVert (geometry.b R))
      (e.walk.getVert (geometry.b R - 2)) = 2 := by
    rw [SimpleGraph.dist_comm, ExtendedPath.distance e (by omega) (by omega)]
    omega
  let : Finite (U R (e.walk.getVert (geometry.b R))) :=
    Nat.finite_of_card_ne_zero (by rw [common.natural.card_at _ hd]; decide)
  let : Finite (⁅Z R (e.walk.getVert (geometry.b R)),
      Q R (e.walk.getVert (geometry.b R - 2))⁆ : Subgroup (FreeAmalgam R)) :=
    Finite.of_injective (inclusion (LocalCommutator.displacement_le_U common hd hdist))
      (inclusion_injective _)
  exact eq_of_le_of_card_ge (commutator_mono le_rfl (actor_le_kernel hb e))
    ((LocalCommutator.displacement_card_le_four common hd hdist).trans_eq product.card.symm)

/-- The one selected product gives radius fixation and the order-four lower
bound on H at every M-vertex, with the actual inverse-conjugation action. -/
theorem fixed_and_H_lower_of_product (common : CommonFacts R source geometry)
    (hb : 6 < geometry.b R)
    (sections : ∀ c, color R c = false →
      Nonempty (Escape.NaturalSectionAt c (V R c) (Z R c)))
    {a : Vertex R} (e : RegularPaths.ExtendedPath geometry a)
    (product : ProductCalculation e) :
    (∀ c, color R c = false → ⁅V R c, Q R c⁆ ≤ fixedCore R c) ∧
      ∀ c, color R c = false → 4 ≤ Nat.card (H R c) := by
  let v := e.walk.getVert (geometry.b R - 2)
  have heven : Even (geometry.b R - 2) := by
    have he := geometry.even (alpha R) rfl
    change Even (geometry.b R) at he
    rw [Nat.even_iff] at he ⊢
    omega
  have hv : color R v = false := ExtendedPath.vertex_color e heven (by omega)
  obtain ⟨sv⟩ := sections v hv
  have hdis : ⁅Z R (e.walk.getVert (geometry.b R)), Q R v⁆ ≤ fixedCore R v := by
    rw [← product_eq_displacement common hb e product]
    exact product.fixed
  have hfixed : ⁅V R v, Q R v⁆ ≤ fixedCore R v :=
    radius_fixed_of_moving common hv sv (opposite_moving common hb e) hdis
  let := finite_stabilizer R v
  let : Finite (H R v) := Finite.of_injective
    (inclusion (((H_le_commutator R v).trans hfixed).trans
      (inf_le_left.trans (show Q R v ≤ stabilizer R v from fun _ hx => hx.1))))
    (inclusion_injective _)
  have hcard : 4 ≤ Nat.card (H R v) := by
    simpa only [product.card] using card_le_of_le (product_le_H common hb e)
  constructor
  · intro c hc
    obtain ⟨u, hu⟩ := exists_mVertex_of_color R hv
    obtain ⟨w, hw⟩ := exists_mVertex_of_color R hc
    let g := u⁻¹ * w
    have hg : act R g v = c := by rw [hu, act_mVertex, mul_inv_cancel_left, ← hw]
    have hh := map_mono (f := (MulAut.conj g⁻¹).toMonoidHom) hfixed
    rwa [map_commutator, ← V_act, ← Q_act, ← Escape.EdgeTransfer.fixedCore_act, hg] at hh
  · intro c hc
    rwa [Escape.Initial.H_card_eq_base v hv, ← Escape.Initial.H_card_eq_base c hc] at hcard

/-- Every moving incident edge equals H at its center: natural-section
generation supplies containment and the two order bounds force equality. -/
theorem moving_edge_eq_H_of_product (common : CommonFacts R source geometry)
    (hb : 6 < geometry.b R)
    (sections : ∀ c, color R c = false →
      Nonempty (Escape.NaturalSectionAt c (V R c) (Z R c)))
    {a : Vertex R} (e : RegularPaths.ExtendedPath geometry a)
    (product : ProductCalculation e) {c t d : Vertex R}
    (hc : color R c = false) (hct : Adjacent R c t) (hdt : Adjacent R d t)
    (hd : d ∈ Escape.movingNeighbors geometry c) : edgeCommutator R d t = H R c := by
  obtain ⟨hfixed, hlower⟩ := fixed_and_H_lower_of_product common hb sections e product
  have hdc := Escape.EdgeTransfer.neighbor_color c t d hc hct hdt
  have hZV : Z R d ≤ V R c := le_iSup_of_le d
    (le_iSup_of_le (by rw [SimpleGraph.dist_comm, hd.1]) le_rfl)
  obtain ⟨s⟩ := sections c hc
  have hHC := H_le_moving_displacement common hc s hd
    ((commutator_mono hZV le_rfl).trans (hfixed c hc))
  have ht : color R t = true := by
    have hn := adjacent_color_ne R hct
    cases h : color R t <;> simp_all
  have hHE : H R c ≤ edgeCommutator R d t := hHC.trans
    (commutator_mono le_rfl (Q_le_adjacent_h R ht hct))
  let : Finite (U R d) := Nat.finite_of_card_ne_zero
    (by rw [common.natural.card_at d hdc]; decide)
  let : Finite (edgeCommutator R d t) := Finite.of_injective
    (inclusion (Escape.EdgeTransfer.edge_commutator_le_natural common.large_distance
      (LocalCommutator.moduleFacts common) d t hdc hdt)) (inclusion_injective _)
  exact (eq_of_le_of_card_ge hHE
    ((Escape.EdgeTransfer.edge_displacement_card_le_four common.large_distance
      (LocalCommutator.moduleFacts common) d t hdc hdt).trans (hlower c hc))).symm

/-- The symmetric assertion on p.895, conditional on the independent literal
product calculation and the preceding full natural sections. -/
theorem movingEdgeFixed_of_product (common : CommonFacts R source geometry)
    (hb : 6 < geometry.b R)
    (sections : ∀ c, color R c = false →
      Nonempty (Escape.NaturalSectionAt c (V R c) (Z R c)))
    {a : Vertex R} (e : RegularPaths.ExtendedPath geometry a)
    (product : ProductCalculation e) : MovingEdgeFixed geometry := by
  intro c t d hc hct hdt hd
  rw [moving_edge_eq_H_of_product common hb sections e product hc hct hdt hd]
  exact (H_le_commutator R c).trans
    ((fixed_and_H_lower_of_product common hb sections e product).1 c hc)

/-- Apply the existing (4.2)(i) and (iii) transfers to obtain centrality in
the whole stabilizer. The product premise remains with final source assembly. -/
theorem local_centrality_of_product (common : CommonFacts R source geometry)
    (hb : 6 < geometry.b R)
    (sections : ∀ c, color R c = false →
      Nonempty (Escape.NaturalSectionAt c (V R c) (Z R c)))
    {a : Vertex R} (e : RegularPaths.ExtendedPath geometry a)
    (product : ProductCalculation e) {c : Vertex R} (hc : color R c = false) :
    ⁅V R c, Q R c⁆ ≤ (center (stabilizer R c)).map (stabilizer R c).subtype :=
  centrality_at_all common (movingEdgeFixed_of_product common hb sections e product) sections e hc

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality.FinalCalculation.Conclusion.SymmetricSource
