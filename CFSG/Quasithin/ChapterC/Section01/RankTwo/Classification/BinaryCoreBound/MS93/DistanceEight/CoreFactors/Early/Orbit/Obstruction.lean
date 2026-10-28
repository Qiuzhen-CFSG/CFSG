module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.CoreFactors.Early.Statements
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.CoreFactors.Early.Moving
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.PathCentrality.LocalCommutator.Basic
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.PairingControl.Basic


/-!
# The relative-normalizer obstruction in MS93 (4.5.2)

The source defines G_(a,t) as N_(G_a)(Q_t) on printed p.881 when the two
edge indices have the values supplied by `Earlier`. The generation clause
of `OrbitFacts` instead uses the edge stabilizer G_a ∩ G_t. Moreover, its
outer Set annotation makes the displayed sup elaborate as set union.

Even replacing that union by a genuine subgroup join does not repair the
statement. The order-two subgroup H_(a-2) ∩ H_(a+2) lies in U_a, by moving
generation and the genuine (4.4) centrality. It is centralized by the edge
stabilizer, the critical endpoint Z_(a+8), and C_a. Thus their product cannot
cover G_a, since U_a has no nontrivial local fixed subgroup. The final export
applies this obstruction to the literal published output contract.

This is a diagnostic of the local interface, not a counterexample to the
source theorem or a construction of its orbit layers. No existence of the
supplied preceding-source witnesses is asserted. The source assembly must
retain the relative normalizer and an explicitly typed subgroup join.

Source: Meierfrankenfeld--Stellmacher, Pushing up weak BN-pairs of rank two
(1993), Section 4 notation, p.881; (4.4)--(4.5.2), pp.890, 896--897.
-/

public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
open scoped Pointwise
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.CoreFactors.Early.Orbit
open PathCentrality PathCentrality.RegularPaths
variable {M : Type*} [Group M] {L R : Subgroup M} {geometry : Geometry R}
  {source : LocalSource L R}

private theorem source_shortest {a : Vertex R} (p : SourcePath R a) :
    p.walk.length = (cosetGraph R).dist p.first p.last := by
  obtain ⟨w, hw⟩ := (cosetGraph_connected R).exists_walk_length_eq_dist p.first p.last
  have heq : p.walk = w := Subtype.mk.inj
    ((cosetGraph_isTree R).isAcyclic.subsingleton_path p.first p.last |>.elim
      ⟨p.walk, p.isPath⟩ ⟨w, w.isPath_of_length_eq_dist hw⟩)
  rw [heq]
  exact hw

private theorem segment_distance {a : Vertex R} (p : SourcePath R a)
    {i j : ℕ} (hij : i ≤ j) (hj : j ≤ 14) :
    (cosetGraph R).dist (p.walk.getVert i) (p.walk.getVert j) = j - i := by
  have hh := SimpleGraph.length_eq_dist_of_subwalk
    (SimpleGraph.length_eq_dist_of_subwalk (source_shortest p) (p.walk.isSubwalk_drop i))
    ((p.walk.drop i).isSubwalk_take (j - i))
  have hmin : j - i ≤ p.walk.length - i := by rw [p.length_eq]; omega
  simpa only [SimpleGraph.Walk.take_length, SimpleGraph.Walk.drop_length,
    inf_eq_left.mpr hmin, SimpleGraph.Walk.drop_getVert, Nat.add_sub_of_le hij] using hh.symm

private theorem path_color {a : Vertex R} (p : SourcePath R a)
    {i : ℕ} (hi : Even i) (hi' : i ≤ 14) :
    color R (p.walk.getVert i) = false :=
  (walk_vertex_color p.start_color p.walk (by rw [p.length_eq]; exact hi')).mpr hi

private theorem path_adjacent {a : Vertex R} (p : SourcePath R a) {i : ℕ} (hi : i < 14) :
    Adjacent R (p.walk.getVert i) (p.walk.getVert (i + 1)) :=
  (cosetGraph_adj R _ _).mp (p.walk.adj_getVert_succ (by rw [p.length_eq]; exact hi))

private theorem forward_moving [Finite M] (common : CommonFacts R source geometry)
    (earlier : Earlier R geometry) {a : Vertex R} (p : SourcePath R a)
    {i : ℕ} (hi : Even i) (hi2 : 2 ≤ i) (hi8 : i ≤ 8) :
    p.walk.getVert (i + 2) ∈ Escape.movingNeighbors geometry (p.walk.getVert i) := by
  have he : Even (i - 2) := by rw [Nat.even_iff] at hi ⊢; omega
  have hstart := path_color p he (by omega)
  have hend := path_color p (i := i - 2 + 8) (by rw [Nat.even_iff] at he ⊢; omega) (by omega)
  have hcrit : CriticalPair R (p.walk.getVert (i - 2)) (p.walk.getVert (i - 2 + 8))
      (geometry.exists_critical _ hstart) := by
    refine ⟨?_, (p.critical (i - 2) he (by omega)).2⟩
    rw [geometry.distance_constant _ hstart]
    change _ = geometry.b R
    rw [earlier.distance]
    exact (p.critical (i - 2) he (by omega)).1
  have hr := common.critical_reverse _ hstart _ hend hcrit
  have hback : p.walk.getVert (i - 2) ∈ Escape.movingNeighbors geometry (p.walk.getVert i) := by
    apply Escape.Propagation.RadiusFour.Forward.Reversal.critical_endpoint_moving
      source common.large_distance hend hr
    constructor
    · rw [SimpleGraph.dist_comm, segment_distance p (by omega) (by omega)]
      omega
    · rw [SimpleGraph.dist_comm (u := p.walk.getVert (i - 2 + 8)),
        SimpleGraph.dist_comm (u := p.walk.getVert (i - 2 + 8)),
        segment_distance p (by omega) (by omega), segment_distance p (by omega) (by omega)]
      omega
  obtain ⟨g, hg, ht⟩ := p.turns i hi hi2 (by omega)
  have hact := Escape.Propagation.Rigidity.moving_of_local_act common.large_distance
    (p.walk.getVert i) (p.walk.getVert (i - 2)) (path_color p hi (by omega)) hback g⁻¹
    ((stabilizer R (p.walk.getVert i)).inv_mem hg)
  rw [← ht, ← act_mul, mul_inv_cancel, act_one] at hact
  exact hact

/-- Moving generation and (4.4) centrality put H in the initial displacement,
without using the contrary configuration from (4.3). -/
theorem H_le_displacement [Finite M] (common : CommonFacts R source geometry)
    (earlier : Earlier R geometry) {a d : Vertex R} (ha : color R a = false)
    (hd : d ∈ Escape.movingNeighbors geometry a) : H R a ≤ ⁅Z R d, Q R a⁆ := by
  have hspan := moving_le_hatV source earlier ha hd
  have hda : (cosetGraph R).dist d a = 2 := by rw [SimpleGraph.dist_comm]; exact hd.1
  have hKC : ⁅Z R d, Q R a⁆ ≤ (center (stabilizer R a)).map (stabilizer R a).subtype :=
    (commutator_mono ((Z_le_localZSpan R d a).trans (localZSpan_le_V R hda.le)) le_rfl).trans
      (earlier.centrality a ha)
  have hKcentral : ⁅Z R d, Q R a⁆ ≤ centralizer (stabilizer R a : Set (FreeAmalgam R)) := by
    intro x hx y hy
    obtain ⟨z, hz, rfl⟩ := hKC hx
    exact congrArg Subtype.val (mem_center_iff.mp hz ⟨y, hy⟩)
  have hKn : stabilizer R a ≤ normalizer ((⁅Z R d, Q R a⁆ : Subgroup (FreeAmalgam R)) : Set (FreeAmalgam R)) :=
    (le_centralizer_iff.mp hKcentral).trans (Subgroup.centralizer_le_normalizer _)
  have hlocal : ⁅hatV R a d, Q R a⁆ = ⁅Z R d, Q R a⁆ := by
    rw [hatV, LocalCommutator.span_commutator_eq_conjugates ha hda.le common.large_distance]
    exact Escape.PairingControl.conjugatesIn_eq_of_normalized _ _ hKn
  exact (commutator_mono hspan le_rfl).trans hlocal.le


/-- The preceding fixed commutator at a moving neighbor lies in the actual
natural subgroup at the other vertex. -/
theorem H_le_neighbor_U [Finite M] (common : CommonFacts R source geometry)
    (earlier : Earlier R geometry) {a d : Vertex R} (ha : color R a = false)
    (hd : d ∈ Escape.movingNeighbors geometry a) : H R a ≤ U R d := by
  have hdc : color R d = false :=
    (color_eq_of_dist_even R a d (by rw [hd.1]; decide)).symm.trans ha
  exact (H_le_displacement common earlier ha hd).trans
    ((commutator_mono le_rfl (Q_le_stabilizer_of_dist_two R a d ha hd.1)).trans
      (Escape.Initial.Z_commutator_stabilizer source d hdc).le)

private theorem H_centralizes_local (earlier : Earlier R geometry)
    {a : Vertex R} (ha : color R a = false) :
    H R a ≤ centralizer (stabilizer R a : Set (FreeAmalgam R)) := by
  intro x hx y hy
  obtain ⟨z, hz, rfl⟩ := H_le_localCenter_of_central R a (earlier.centrality a ha) hx
  exact congrArg Subtype.val (mem_center_iff.mp hz ⟨y, hy⟩)

/-- Even the subgroup-generated edge-stabilizer product cannot cover G_a.
This is stronger than the obstruction to the set union currently elaborated
in OrbitFacts. The source uses the relative normalizer defined on p.881. -/
theorem edge_stabilizer_product_not_cover [Finite M] (common : CommonFacts R source geometry)
    (earlier : Earlier R geometry) {a : Vertex R} (p : SourcePath R a)
    (first : FirstFactsOnPath R geometry p) :
    ¬ (stabilizer R a : Set (FreeAmalgam R)) ⊆
      (((stabilizer R a ⊓ stabilizer R (p.walk.getVert 3)) ⊔ Z R (p.walk.getVert 12) :
        Subgroup (FreeAmalgam R)) : Set (FreeAmalgam R)) * (C R a : Set (FreeAmalgam R)) := by
  intro hgen
  let J := H R (p.walk.getVert 2) ⊓ H R (p.walk.getVert 6)
  have h2 := path_color p (i := 2) (by decide) (by decide)
  have h4 := path_color p (i := 4) (by decide) (by decide)
  have h6 := path_color p (i := 6) (by decide) (by decide)
  have h12 := path_color p (i := 12) (by decide) (by decide)
  have ha : color R a = false := p.center_eq ▸ h4
  have hJU : J ≤ U R a := by
    have hmov := forward_moving common earlier p (i := 2) (by decide) (by decide) (by decide)
    have hU := H_le_neighbor_U common earlier h2 hmov
    change H R (p.walk.getVert 2) ≤ U R (p.walk.getVert 4) at hU
    rw [p.center_eq] at hU
    exact inf_le_left.trans hU
  have hJedge : J ≤ centralizer
      (↑(stabilizer R a ⊓ stabilizer R (p.walk.getVert 3)) : Set (FreeAmalgam R)) := by
    have ht : color R (p.walk.getVert 3) = true := by
      have hn := adjacent_color_ne R (path_adjacent p (i := 2) (by decide))
      cases h : color R (p.walk.getVert 3) <;> simp_all
    have hadj : Adjacent R a (p.walk.getVert 3) := by
      simpa only [p.center_eq] using adjacent_symm R (path_adjacent p (i := 3) (by decide))
    rw [← Q_h_eq_edge R ht hadj]
    exact (inf_le_left.trans (H_centralizes_local earlier h2)).trans
      (centralizer_le (show Q R (p.walk.getVert 3) ≤ stabilizer R (p.walk.getVert 2) from
        fun _ hx => hx.2 _ (adjacent_symm R (path_adjacent p (i := 2) (by decide)))))
  have hJend : J ≤ centralizer (Z R (p.walk.getVert 12) : Set (FreeAmalgam R)) := by
    have hZQ : Z R (p.walk.getVert 12) ≤ Q R (p.walk.getVert 6) := by
      apply Z_le_Q_of_dist_lt R _ (geometry.exists_critical _ h12)
      rw [geometry.distance_constant _ h12]
      change _ < geometry.b R
      rw [earlier.distance, SimpleGraph.dist_comm, segment_distance p (by decide) (by decide)]
      decide
    exact (inf_le_right.trans (H_le_Z_of_central common h6 (earlier.centrality _ h6))).trans
      ((commutator_eq_bot_iff_le_centralizer.mp (geometry.centralizes _ h6)).trans
        (centralizer_le hZQ))
  have hJC : C R a ≤ centralizer (J : Set (FreeAmalgam R)) :=
    inf_le_right.trans (centralizer_le (hJU.trans (U_le_Z R a)))
  have hfix : stabilizer R a ≤ centralizer (J : Set (FreeAmalgam R)) := by
    intro x hx
    have hxprod : x ∈
        (((stabilizer R a ⊓ stabilizer R (p.walk.getVert 3)) ⊔ Z R (p.walk.getVert 12) :
          Subgroup (FreeAmalgam R)) : Set (FreeAmalgam R)) * (C R a : Set (FreeAmalgam R)) := hgen hx
    obtain ⟨y, hy, z, hz, rfl⟩ := hxprod
    exact (centralizer (J : Set (FreeAmalgam R))).mul_mem
      (sup_le (le_centralizer_iff.mp hJedge) (le_centralizer_iff.mp hJend) hy) (hJC hz)
  have hbot : J = ⊥ := by
    apply le_bot_iff.mp
    rw [← Escape.EdgeTransfer.U_fixed_eq_bot (LocalCommutator.moduleFacts common) a ha]
    exact le_inf hJU ((le_centralizer_iff.mp hfix).trans (centralizer_le (Ltilde_le_stabilizer a)))
  have ff := first.forward 2 (by decide) (by decide) (by decide)
  have hcard : Nat.card J = 2 := by
    change Nat.card (H R (p.walk.getVert 2) ⊓ H R (p.walk.getVert (2 + 4)) :
      Subgroup (FreeAmalgam R)) = 2
    rw [← ff.commutator_eq]
    exact ff.commutator_card
  rw [hbot, Subgroup.card_bot] at hcard
  omega

/-- The old edge-stabilizer transcription cannot be the output of the early
source assembly. This diagnoses the contract; it is not a proof of (4.5.2). -/
theorem not_orbitFacts [Finite M] (common : CommonFacts R source geometry)
    (earlier : Earlier R geometry) {a : Vertex R} (p : SourcePath R a)
    (first : FirstFactsOnPath R geometry p) : ¬ Nonempty (OrbitFacts R p) := by
  rintro ⟨facts⟩
  apply edge_stabilizer_product_not_cover common earlier p first
  intro x hx
  have hxprod := facts.local_generation.symm ▸ hx
  obtain ⟨y, hy, z, hz, rfl⟩ := hxprod
  refine ⟨y, ?_, z, hz, rfl⟩
  change y ∈ ((stabilizer R a ⊓ stabilizer R (p.walk.getVert 3)) ⊔
    Z R (p.walk.getVert 12) : Subgroup (FreeAmalgam R))
  rcases hy with hy | hy
  · exact mem_sup_left hy
  · exact mem_sup_right hy

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.CoreFactors.Early.Orbit
