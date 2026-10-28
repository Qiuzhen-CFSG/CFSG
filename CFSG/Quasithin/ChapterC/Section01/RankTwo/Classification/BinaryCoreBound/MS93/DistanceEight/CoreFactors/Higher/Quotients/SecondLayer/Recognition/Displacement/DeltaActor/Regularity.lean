module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.CoreFactors.Higher.Quotients.SecondLayer.Recognition.Displacement.DeltaActor.Nondegeneracy
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.CoreFactors.Higher.OrbitGeometry.Replacement.Unequal
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.CoreFactors.Higher.Quotients.SecondLayer.Recognition.Displacement.DeltaActor.Regularity.SeedExtension
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.CoreFactors.Higher.Quotients.SecondLayer.Recognition.Displacement.DeltaActor.Regularity.CriticalWindow

/-!
# The regular four-segment through the given delta

The actual delta transporter and generation equation determine a geodesic
four-segment delta--c--a. Its unequal edge Z-layers require the literal
relative-normalizer clause (4.5.2)(i). In the notation of printed p.881 this
actor is G_c intersect N(Q_t), not merely G_c intersect G_t. The binary
edge-centralizer theorem turns equal edge Z-layers into normalization of Q_t;
source normality would then give Z_delta = Z_a, contradicting generation.

`delta_regular_four_segment` retains the original delta and constructs the
shortest walk, its middle vertex and edge, the turn and the Z-inequality.
The SeedExtension leaf proves that a separated regular critical eight-window
extends to the full fourteen-edge SourcePath while preserving every vertex of
that seed. Its equivalence identifies the exact remaining geometric obligation.
The conditional backward construction follows the original path backwards from
a, with only the additional criticality guard Z_delta not contained in Q_(p[0]).
All turns and separations are discharged. The guard itself remains unproved;
this is not a construction from DeltaChoice alone. Generation and independence
alone do not imply that guard.

The CriticalWindow leaf now supplies a different regular critical eight-window
through the same delta,c,a, from the original instance of (4.5.4)(ii).
Generation and the original product force its critical endpoint; all turns
are proved. Its middle edge-Z separation remains open, but the proved
`window_hatW_product` requires only the regular critical window and yields
the needed delta actor product. The actual displacement consumer is proved
there without a new path or product premise. The preceding orbit-containment
source input remains with qt-c01-ms93-higher-orbit-geometry.

`sourcePathAct` preserves every SourcePath field. Its concrete consumer shows
that a weaker geometric witness suffices for the original product application:
after transporting p by delta's transporter, an element of G_delta need only
align the final two kernels, not the corresponding vertices. This alignment
remains an explicit, undischarged premise; the theorem is not the completed
source delta argument. It reuses the parent's proved actor transport and
candidate-product consumer, without another quotient calculation.

The earlier inputs are (4.5.3)(i) at c, already permitted by the parent, and
(4.5.2)(i) at the original a,t,c of the supplied path. Their producer remains
qt-c01-ms93-core-factors-early-layers. The last theorem uses the universally
guarded literal (4.5.1)(iv), delta's orbit-containment clause (4.5.4)(ii),
and the original (4.5.3)(iii), with the same producers as DeltaActor.Transport.

Source: Meierfrankenfeld--Stellmacher, *Pushing up weak BN-pairs of rank two*
(1993), notation p.881; (4.5.1)--(4.5.4), printed pp.896--899.
-/

@[expose] public section
open Subgroup Stellmacher.PushingUp.AmalgamGraph
open scoped Pointwise commutatorElement
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.CoreFactors.Higher.Quotients.SecondLayer.Recognition.Displacement.Regularity
open PathCentrality
variable {M : Type*} [Group M] {R L : Subgroup M}
  {geometry : Geometry R} {source : LocalSource L R}

/-- Transport all fields of the standing source path by the actual right action. -/
def sourcePathAct {a : Vertex R} (p : Higher.SourcePath a) (g : FreeAmalgam R) :
    Higher.SourcePath (act R g a) where
  first := act R g p.first
  last := act R g p.last
  walk := actWalk R g p.walk
  start_color := (action_preserves_color R g _).trans p.start_color
  length_eq := (actWalk_length R g p.walk).trans p.length_eq
  shortest := by rw [actWalk_length, dist_act]; exact p.shortest
  center_eq := by rw [actWalk_getVert, p.center_eq]
  turns := by
    intro i hi hi2 hi12
    obtain ⟨h, hh, ht⟩ := p.turns i hi hi2 hi12
    refine ⟨g⁻¹ * h * g, ?_, ?_⟩
    · rw [actWalk_getVert, stabilizer_act]
      simpa only [MulAut.conj_apply, inv_inv, MulEquiv.toMonoidHom_eq_coe,
        MonoidHom.coe_coe] using mem_map_of_mem (MulAut.conj g⁻¹).toMonoidHom hh
    · rw [actWalk_getVert, actWalk_getVert, ← act_mul]
      simp only [← mul_assoc, mul_inv_cancel, one_mul, act_mul, ht]
  critical := by
    intro i hi hi6
    rw [actWalk_getVert, actWalk_getVert, dist_act, Z_act, Q_act]
    exact ⟨(p.critical i hi hi6).1, fun h => (p.critical i hi hi6).2
      ((map_le_map_iff_of_injective (MulAut.conj g⁻¹).injective).mp h)⟩
  distinct_Z := by
    intro i hi hi2 hi12
    rw [actWalk_getVert, actWalk_getVert, Z_act, Z_act]
    exact fun he => p.distinct_Z i hi hi2 hi12
      ((Subgroup.map_injective (MulAut.conj g⁻¹).injective) he)

/-- The literal relative-normalizer clause of (4.5.2)(i) separates the two
edge Z-layers for the specified delta. Its source guard is the original p;
the supplied edge-stabilizer normality alone is not used as this clause. -/
theorem delta_edge_Z_ne [Finite M] (common : CommonFacts R source geometry)
    (earlier : Earlier R geometry) {p : Higher.SourcePath (alpha R)} (δ : DeltaChoice p)
    (hVc : hatV R (p.walk.getVert 6) (p.walk.getVert 8) =
      Vcirc R (p.walk.getVert 6) ⊔ Z R (p.walk.getVert 6))
    (hrelative : stabilizer R (p.walk.getVert 6) ⊓
      normalizer (Q R (p.walk.getVert 5) : Set (FreeAmalgam R)) ≤
        normalizer (Z R (alpha R) : Set (FreeAmalgam R))) :
    Z R (act R δ.transporter (p.walk.getVert 5)) ≠ Z R (p.walk.getVert 5) := by
  intro he
  have hc : color R (p.walk.getVert 6) = false :=
    (PathCentrality.RegularPaths.walk_vertex_color p.start_color p.walk
      (by rw [p.length_eq]; decide)).mpr (by decide)
  have hct : Adjacent R (p.walk.getVert 6) (p.walk.getVert 5) :=
    adjacent_symm R ((cosetGraph_adj R _ _).mp
      (p.walk.adj_getVert_succ (i := 5) (by rw [p.length_eq]; decide)))
  have hn : (δ.transporter : FreeAmalgam R)⁻¹ ∈
      normalizer (Z R (p.walk.getVert 5) : Set (FreeAmalgam R)) := by
    apply mem_normalizer_iff_map_conj_eq.mpr
    rwa [Z_act] at he
  have hq := Higher.OrbitGeometry.Replacement.Unequal.edge_Z_normalizer_le
    common earlier hc hct ⟨(stabilizer R _).inv_mem δ.transporter.property, hn⟩
  have hz : Z R δ.vertex = Z R (alpha R) := by
    rw [δ.vertex_eq, Z_act]
    exact mem_normalizer_iff_map_conj_eq.mp (hrelative hq)
  apply delta_seed_not_le_pair common earlier δ hVc
  rw [hz]
  exact le_sup_left

/-- The actual delta four-segment is geodesic, has the required middle
vertex and edge, has its genuine turn, and has unequal edge Z-layers.
No critical eight-window or fourteen-edge extension is asserted. -/
theorem delta_regular_four_segment [Finite M] (common : CommonFacts R source geometry)
    (earlier : Earlier R geometry) {p : Higher.SourcePath (alpha R)} (δ : DeltaChoice p)
    (hVc : hatV R (p.walk.getVert 6) (p.walk.getVert 8) =
      Vcirc R (p.walk.getVert 6) ⊔ Z R (p.walk.getVert 6))
    (hrelative : stabilizer R (p.walk.getVert 6) ⊓
      normalizer (Q R (p.walk.getVert 5) : Set (FreeAmalgam R)) ≤
        normalizer (Z R (alpha R) : Set (FreeAmalgam R))) :
    ∃ w : (cosetGraph R).Walk δ.vertex (alpha R),
      w.length = 4 ∧ w.length = (cosetGraph R).dist δ.vertex (alpha R) ∧
      w.getVert 1 = act R δ.transporter (p.walk.getVert 5) ∧
      w.getVert 2 = p.walk.getVert 6 ∧ w.getVert 3 = p.walk.getVert 5 ∧
      Z R (w.getVert 1) ≠ Z R (w.getVert 3) ∧
      ∃ g ∈ stabilizer R (w.getVert 2), act R g (w.getVert 4) = w.getVert 0 := by
  have hat : (cosetGraph R).Adj (alpha R) (p.walk.getVert 5) := by
    simpa only [p.center_eq] using p.walk.adj_getVert_succ (i := 4)
      (by rw [p.length_eq]; decide)
  have htc : (cosetGraph R).Adj (p.walk.getVert 5) (p.walk.getVert 6) :=
    p.walk.adj_getVert_succ (i := 5) (by rw [p.length_eq]; decide)
  have hδt : (cosetGraph R).Adj δ.vertex (act R δ.transporter (p.walk.getVert 5)) := by
    rw [δ.vertex_eq]
    exact (cosetGraph_adj R _ _).mpr ((adjacent_act_iff R δ.transporter _ _).mpr
      ((cosetGraph_adj R _ _).mp hat))
  have hct : (cosetGraph R).Adj (act R δ.transporter (p.walk.getVert 5))
      (p.walk.getVert 6) := by
    have hh := (adjacent_act_iff R δ.transporter _ _).mpr ((cosetGraph_adj R _ _).mp htc)
    have hf : act R δ.transporter (p.walk.getVert 6) = p.walk.getVert 6 := δ.transporter.property
    rw [hf] at hh
    exact (cosetGraph_adj R _ _).mpr hh
  let w := SimpleGraph.Walk.cons hδt (.cons hct (.cons htc.symm (.cons hat.symm .nil)))
  have hweak : stabilizer R (p.walk.getVert 6) ⊓ stabilizer R (p.walk.getVert 5) ≤
      normalizer (Z R (alpha R) : Set (FreeAmalgam R)) :=
    (inf_le_inf_left _ (Q_normalized R _)).trans hrelative
  refine ⟨w, rfl, ?_, rfl, rfl, rfl, ?_, δ.transporter, δ.transporter.property, ?_⟩
  · change 4 = _
    rw [SimpleGraph.dist_comm, delta_dist_base_eq_four common earlier δ hVc hweak]
  · exact delta_edge_Z_ne common earlier δ hVc hrelative
  · exact δ.vertex_eq.symm

private theorem hatW_act (g : FreeAmalgam R) (a c d : Vertex R) :
    hatW R (act R g a) (act R g c) (act R g d) =
      (hatW R a c d).map (MulAut.conj g⁻¹).toMonoidHom := by
  simp only [hatW, hatV_eq_conjugatesIn, Z_act, stabilizer_act,
    CriticalCriterion.conjugatesIn_map]

/-- A weaker geometric witness suffices for the literal product: after
transporting p by delta's given transporter, an element fixing delta aligns
the endpoint kernel and the preceding edge kernel. It need not align vertices.
All source-path fields are retained by `sourcePathAct`. Existence of h is
not asserted; in particular this is not completion of (4.5.4)(iii). -/
theorem delta_small_and_separated_of_kernel_alignment [Finite M]
    (source : LocalSource L R) (common : CommonFacts R source geometry)
    (earlier : Earlier R geometry) {p : Higher.SourcePath (alpha R)} (δ : DeltaChoice p)
    (s : OrbitModule source p δ.vertex)
    (h : FreeAmalgam R) (hh : h ∈ stabilizer R δ.vertex)
    (hendpoint : Q R (act R h (act R δ.transporter (p.walk.getVert 8))) = Q R (alpha R))
    (hedge : Q R (act R h (act R δ.transporter (p.walk.getVert 7))) = Q R (p.walk.getVert 5))
    (hproducts : ∀ (v : Vertex R) (r : Higher.SourcePath v),
      (hatW R v (r.walk.getVert 6) (r.walk.getVert 8) : Set (FreeAmalgam R)) *
        (Q R (r.walk.getVert 8) : Set (FreeAmalgam R)) =
          (Q R (r.walk.getVert 7) : Set (FreeAmalgam R)))
    (horbit : NormalizerTransfer.conjugatesIn (Z R δ.vertex)
      (stabilizer R (alpha R)) ≤ Q R δ.vertex)
    (hcomm : ⁅hatW R (alpha R) (p.walk.getVert 6) (p.walk.getVert 8),
      Q R (alpha R)⁆ ≤ Z R (alpha R)) : letI := s.normal
    Escape.Initial.Natural.Splitting.HasSmallInvolution s.action ∧
      DisplacementSeparation s.action common.natural.marking := by
  let r := sourcePathAct (sourcePathAct p δ.transporter) h
  have heq : hatW R (act R h (act R δ.transporter (alpha R)))
      (r.walk.getVert 6) (r.walk.getVert 8) =
      hatW R δ.vertex (p.walk.getVert 6) (alpha R) := by
    change hatW R (act R h (act R δ.transporter (alpha R)))
      ((actWalk R h (actWalk R δ.transporter p.walk)).getVert 6)
      ((actWalk R h (actWalk R δ.transporter p.walk)).getVert 8) = _
    simp only [actWalk_getVert, hatW_act]
    change (NormalizerTransfer.rightConjugate
      (hatW R (alpha R) (p.walk.getVert 6) (p.walk.getVert 8)) δ.transporter).map
        (MulAut.conj h⁻¹).toMonoidHom = _
    rw [← delta_actor_eq_conjugate δ]
    exact mem_normalizer_iff_map_conj_eq.mp
      (hatW_normalized R δ.vertex (p.walk.getVert 6) (alpha R)
        ((stabilizer R δ.vertex).inv_mem hh))
  have hp := hproducts _ r
  rw [heq] at hp
  have h8 : Q R (r.walk.getVert 8) = Q R (alpha R) := by
    change Q R ((actWalk R h (actWalk R δ.transporter p.walk)).getVert 8) = _
    simpa only [actWalk_getVert] using hendpoint
  have h7 : Q R (r.walk.getVert 7) = Q R (p.walk.getVert 5) := by
    change Q R ((actWalk R h (actWalk R δ.transporter p.walk)).getVert 7) = _
    simpa only [actWalk_getVert] using hedge
  rw [h8, h7] at hp
  exact delta_small_and_separated_of_candidate_product source common earlier δ s hp horbit hcomm

/-- The concrete backward continuation needs just one additional criticality
inequality. All its turns, Z-separations and vertex identities are proved here,
then the three replacements preserve this same delta and its fixed segment.
The inequality is not asserted by delta's generation equation. -/
theorem delta_sourcePath_of_original_noncontainment [Finite M]
    (common : CommonFacts R source geometry) (earlier : Earlier R geometry)
    {p : Higher.SourcePath (alpha R)} (δ : DeltaChoice p)
    (hVc : hatV R (p.walk.getVert 6) (p.walk.getVert 8) =
      Vcirc R (p.walk.getVert 6) ⊔ Z R (p.walk.getVert 6))
    (hrelative : stabilizer R (p.walk.getVert 6) ⊓
      normalizer (Q R (p.walk.getVert 5) : Set (FreeAmalgam R)) ≤
        normalizer (Z R (alpha R) : Set (FreeAmalgam R)))
    (hn : ¬ Z R δ.vertex ≤ Q R p.first) :
    ∃ q : Higher.SourcePath δ.vertex,
      q.walk.getVert 6 = p.walk.getVert 6 ∧
      q.walk.getVert 8 = alpha R ∧ q.walk.getVert 7 = p.walk.getVert 5 := by
  obtain ⟨w, hw, _, hw1, hw2, hw3, hsep, g, hg, hturn⟩ :=
    delta_regular_four_segment common earlier δ hVc hrelative
  let r := (p.walk.take 4).reverse.copy p.center_eq rfl
  have hr : r.length = 4 := by
    simp only [r, SimpleGraph.Walk.length_copy, SimpleGraph.Walk.length_reverse,
      SimpleGraph.Walk.take_length, p.length_eq]
    rfl
  let v := w.append r
  have hvlen : v.length = 8 := by rw [SimpleGraph.Walk.length_append, hw, hr]
  have hleft (i : ℕ) (hi : i < 4) : v.getVert i = w.getVert i := by
    simp only [v, SimpleGraph.Walk.getVert_append, hw, if_pos hi]
  have hright (i : ℕ) (hi : i ≤ 4) : v.getVert (i + 4) = p.walk.getVert (4 - i) := by
    simp only [v, SimpleGraph.Walk.getVert_append, hw, if_neg (by omega : ¬ i + 4 < 4),
      Nat.add_sub_cancel, r, SimpleGraph.Walk.getVert_copy, SimpleGraph.Walk.getVert_reverse,
      SimpleGraph.Walk.take_length, SimpleGraph.Walk.take_getVert, p.length_eq]
    congr 1
    omega
  have hv4 : v.getVert 4 = alpha R := (hright 0 (by decide)).trans p.center_eq
  have hv2 : v.getVert 2 = p.walk.getVert 6 := (hleft 2 (by decide)).trans hw2
  have hv3 : v.getVert 3 = p.walk.getVert 5 := (hleft 3 (by decide)).trans hw3
  have hv6 : v.getVert 6 = p.walk.getVert 2 := hright 2 (by decide)
  have hv8 : v.getVert 8 = p.walk.getVert 0 := hright 4 (by decide)
  have hvdist : (cosetGraph R).dist δ.vertex p.first = 8 := by
    have hge := criticalDistance_le R δ.vertex
      (geometry.exists_critical _ (delta_color δ)) hn
    have he := (geometry.distance_constant _ (delta_color δ)).trans earlier.distance
    rw [he] at hge
    exact le_antisymm ((SimpleGraph.dist_le v).trans_eq hvlen) hge
  let s : CriticalPath R geometry δ.vertex p.first := {
    start_color := delta_color δ
    walk := v
    shortest := hvlen.trans hvdist.symm
    critical := ⟨hvdist.trans (earlier.distance.symm.trans
      (geometry.distance_constant _ (delta_color δ)).symm), hn⟩ }
  have hs : HasTurnConjugators R s := by
    intro i hi hi2 hiend
    change i + 2 ≤ v.length at hiend
    rw [hvlen] at hiend
    have hic : i = 2 ∨ i = 4 ∨ i = 6 := by rw [Nat.even_iff] at hi; omega
    rcases hic with rfl | rfl | rfl
    · refine ⟨g, ?_, ?_⟩
      · change g ∈ stabilizer R (v.getVert 2)
        rwa [hleft 2 (by decide)]
      · change act R g (v.getVert 4) = v.getVert 0
        rw [hv4, hleft 0 (by decide)]
        simpa only [← hw, SimpleGraph.Walk.getVert_length] using hturn
    · obtain ⟨k, hk, ht⟩ := p.turns 4 (by decide) (by decide) (by decide)
      refine ⟨k⁻¹, ?_, ?_⟩
      · change k⁻¹ ∈ stabilizer R (v.getVert 4)
        rw [hv4, ← p.center_eq]
        exact (stabilizer R _).inv_mem hk
      · change act R k⁻¹ (v.getVert 6) = v.getVert 2
        rw [hv6, hv2]
        have h := congrArg (act R k⁻¹) ht
        rw [← act_mul, mul_inv_cancel, act_one] at h
        exact h.symm
    · obtain ⟨k, hk, ht⟩ := p.turns 2 (by decide) (by decide) (by decide)
      refine ⟨k⁻¹, ?_, ?_⟩
      · change k⁻¹ ∈ stabilizer R (v.getVert 6)
        rw [hv6]
        exact (stabilizer R _).inv_mem hk
      · change act R k⁻¹ (v.getVert 8) = v.getVert 4
        rw [hv8, hv4]
        have h := congrArg (act R k⁻¹) ht
        rw [← act_mul, mul_inv_cancel, act_one] at h
        simpa only [p.center_eq] using h.symm
  have hss : ∀ i, Even i → 2 ≤ i → i + 2 ≤ s.walk.length →
      Z R (s.walk.getVert (i - 1)) ≠ Z R (s.walk.getVert (i + 1)) := by
    intro i hi hi2 hiend
    change i + 2 ≤ v.length at hiend
    rw [hvlen] at hiend
    have hic : i = 2 ∨ i = 4 ∨ i = 6 := by rw [Nat.even_iff] at hi; omega
    rcases hic with rfl | rfl | rfl
    · change Z R (v.getVert 1) ≠ Z R (v.getVert 3)
      rw [hleft 1 (by decide), hleft 3 (by decide)]
      exact hsep
    · change Z R (v.getVert 3) ≠ Z R (v.getVert 5)
      rw [hv3, hright 1 (by decide)]
      exact (p.distinct_Z 4 (by decide) (by decide) (by decide)).symm
    · change Z R (v.getVert 5) ≠ Z R (v.getVert 7)
      rw [hright 1 (by decide), hright 3 (by decide)]
      exact (p.distinct_Z 2 (by decide) (by decide) (by decide)).symm
  obtain ⟨q, hq⟩ := sourcePath_of_regular_critical_seed common earlier s hs hss
  exact ⟨q, (hq 2 (by decide)).trans hv2, (hq 4 (by decide)).trans hv4,
    (hq 3 (by decide)).trans hv3⟩


/-- Apply the constructed path to the literal guarded product and the actual
delta orbit module. The backward criticality guard remains explicit; proving
it, or constructing a different regular critical seed, is still required for
the unconditional delta statement. -/
theorem delta_small_and_separated_of_original_noncontainment [Finite M]
    (source : LocalSource L R) (common : CommonFacts R source geometry)
    (earlier : Earlier R geometry) {p : Higher.SourcePath (alpha R)} (δ : DeltaChoice p)
    (s : OrbitModule source p δ.vertex)
    (hVc : hatV R (p.walk.getVert 6) (p.walk.getVert 8) =
      Vcirc R (p.walk.getVert 6) ⊔ Z R (p.walk.getVert 6))
    (hrelative : stabilizer R (p.walk.getVert 6) ⊓
      normalizer (Q R (p.walk.getVert 5) : Set (FreeAmalgam R)) ≤
        normalizer (Z R (alpha R) : Set (FreeAmalgam R)))
    (hn : ¬ Z R δ.vertex ≤ Q R p.first)
    (hproducts : ∀ (v : Vertex R) (r : Higher.SourcePath v),
      (hatW R v (r.walk.getVert 6) (r.walk.getVert 8) : Set (FreeAmalgam R)) *
        (Q R (r.walk.getVert 8) : Set (FreeAmalgam R)) =
          (Q R (r.walk.getVert 7) : Set (FreeAmalgam R)))
    (horbit : NormalizerTransfer.conjugatesIn (Z R δ.vertex)
      (stabilizer R (alpha R)) ≤ Q R δ.vertex)
    (hcomm : ⁅hatW R (alpha R) (p.walk.getVert 6) (p.walk.getVert 8),
      Q R (alpha R)⁆ ≤ Z R (alpha R)) : letI := s.normal
    Escape.Initial.Natural.Splitting.HasSmallInvolution s.action ∧
      DisplacementSeparation s.action common.natural.marking := by
  obtain ⟨q, hc, ha, ht⟩ :=
    delta_sourcePath_of_original_noncontainment common earlier δ hVc hrelative hn
  have hprod := hproducts δ.vertex q
  rw [hc, ha, ht] at hprod
  exact delta_small_and_separated_of_candidate_product source common earlier δ s
    hprod horbit hcomm

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.CoreFactors.Higher.Quotients.SecondLayer.Recognition.Displacement.Regularity
