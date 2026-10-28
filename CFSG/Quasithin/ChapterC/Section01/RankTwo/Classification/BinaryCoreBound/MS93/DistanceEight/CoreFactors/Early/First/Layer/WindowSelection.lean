module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.CoreFactors.Early.First.Layer.EdgeImage

/-!
# The selected calculation on a marked critical window

Only the regular critical window, not the unrelated extra ends of an extended
path, is needed for the two selected commutators. We specialize the construction
and estimates from ProductSource to that window. Each choice retains its
actual conjugator at the start, and the regular midpoint turn places both
selected spans inside the literal hat W. Two nonzero disjoint commutators
therefore force displacement of order at least four.

The fixed-span argument below is the local version of ProductSource.SelectedBounds;
all normality and fixedness occur in the original stabilizer.
Source: Meierfrankenfeld--Stellmacher (1993), printed pp.895--896.
-/

open Subgroup Stellmacher.PushingUp.AmalgamGraph
open scoped Pointwise
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.CoreFactors.Early.First.Layer
open PathCentrality PathCentrality.LocalCommutator NormalizerTransfer
open PathCentrality.FinalCalculation.Conclusion
variable {M : Type*} [Group M] {L R : Subgroup M}
  {source : LocalSource L R} {geometry : Geometry R}

private theorem fixed_span_commutator_le {G : Type*} [Group G]
    (S F Q L D E A : Subgroup G)
    (hgen : L ⊔ Q = F) (hQF : Q ≤ F) (hSQ : S ≤ Q)
    (hFQ : F ≤ normalizer Q) (hFD : F ≤ normalizer D)
    (hDL : D ≤ centralizer (L : Set G)) (hQE : Q ≤ normalizer E)
    (hSE : ⁅S, Q⁆ ≤ E) (hAQ : A ≤ Q)
    (hfixed : ⁅conjugatesIn S F, A⁆ ≤ D) :
    ⁅conjugatesIn S F, A⁆ ≤ E := by
  have hFED : F ≤ normalizer (E ⊓ D : Subgroup G) := by
    rw [← hgen]
    exact sup_le
      ((le_centralizer_iff.mpr (inf_le_right.trans hDL)).trans
        (Subgroup.centralizer_le_normalizer _))
      ((le_inf hQE (hQF.trans hFD)).trans inf_normalizer_le_normalizer_inf)
  have hpre : conjugatesIn S F ≤ commutatorPreimage Q A E := by
    apply iSup_le
    intro g
    have hQ : rightConjugate Q g = Q :=
      mem_normalizer_iff_map_conj_eq.mp (hFQ (F.inv_mem g.property))
    have hD : rightConjugate D g = D :=
      mem_normalizer_iff_map_conj_eq.mp (hFD (F.inv_mem g.property))
    have hED : rightConjugate (E ⊓ D) g = E ⊓ D :=
      mem_normalizer_iff_map_conj_eq.mp (hFED (F.inv_mem g.property))
    have hbound : ⁅rightConjugate S g, A⁆ ≤ rightConjugate E g := by
      apply (commutator_mono le_rfl hAQ).trans
      rw [← hQ, rightConjugate, rightConjugate, ← map_commutator]
      exact map_mono hSE
    have hfix : ⁅rightConjugate S g, A⁆ ≤ D :=
      (commutator_mono (le_iSup (fun h : F => rightConjugate S h) g) le_rfl).trans hfixed
    have hcut : rightConjugate E g ⊓ D = E ⊓ D := by
      calc
        rightConjugate E g ⊓ D = rightConjugate E g ⊓ rightConjugate D g := by rw [hD]
        _ = rightConjugate (E ⊓ D) g :=
          (Subgroup.map_inf _ _ _ (MulAut.conj (g : G)⁻¹).injective).symm
        _ = E ⊓ D := hED
    exact le_commutatorPreimage ((map_mono hSQ).trans hQ.le)
      ((le_inf hbound hfix).trans (hcut.le.trans inf_le_left))
  exact (commutator_mono hpre le_rfl).trans
    (commutator_commutatorPreimage_le Q A E hQE)

private theorem span_commutator_le_edge [Finite M] (source : LocalSource L R)
    (hb : 2 < geometry.b R)
    {a c t : Vertex R} (ha : color R a = false) (hc : color R c = false)
    (hd : (cosetGraph R).dist a c = 2)
    (hat : Adjacent R a t) (hct : Adjacent R c t)
    {A : Subgroup (FreeAmalgam R)} (hA : A ≤ Q R a ⊓ Q R c)
    (hfixed : ⁅localZSpan R a c, A⁆ ≤ fixedCore R c) :
    ⁅localZSpan R a c, A⁆ ≤ edgeCommutator R a t := by
  have ht : color R t = true := by
    have hn := adjacent_color_ne R hat
    rw [ha] at hn
    cases hcol : color R t <;> simp_all
  have hQcQt : Q R c ≤ Q R t := Q_le_adjacent_h R ht hct
  have hQcGa : Q R c ≤ stabilizer R a :=
    Q_le_stabilizer_of_dist_two R c a hc (by rwa [SimpleGraph.dist_comm])
  have hQE : Q R c ≤ normalizer (edgeCommutator R a t) := by
    intro g hg
    apply (mem_normalizer_iff_map_conj_eq).mpr
    change (⁅Z R a, Q R t⁆).map (MulAut.conj g).toMonoidHom = _
    have hZ : (Z R a).map (MulAut.conj g).toMonoidHom = Z R a :=
      mem_normalizer_iff_map_conj_eq.mp (Z_normalized R a (hQcGa hg))
    have hQ : (Q R t).map (MulAut.conj g).toMonoidHom = Q R t :=
      mem_normalizer_iff_map_conj_eq.mp ((Q R t).le_normalizer (hQcQt hg))
    rw [map_commutator, hZ, hQ]
    rfl
  have hZQ : Z R a ≤ Q R c :=
    (Z_le_localZSpan R a c).trans (localZSpan_le_Q R hc hd.le hb)
  rw [LocalCommutator.span_eq_conjugates] at hfixed ⊢
  exact fixed_span_commutator_le (Z R a) (stabilizer R c) (Q R c) (Ltilde R c)
    (fixedCore R c) (edgeCommutator R a t) A (source.local_generation c hc)
    (fun _ hx => hx.1) hZQ (Q_normalized R c) (fixedCore_normalized R c)
    inf_le_right hQE (commutator_mono le_rfl hQcQt) (hA.trans inf_le_right) hfixed


private theorem window_distance (earlier : Earlier R geometry)
    {a f : Vertex R} (p : CriticalPath R geometry a f)
    {i j : ℕ} (hij : i ≤ j) (hj : j ≤ 8) :
    (cosetGraph R).dist (p.walk.getVert i) (p.walk.getVert j) = j - i :=
by
  have hh := SimpleGraph.length_eq_dist_of_subwalk
    (SimpleGraph.length_eq_dist_of_subwalk p.shortest (p.walk.isSubwalk_drop i))
    ((p.walk.drop i).isSubwalk_take (j - i))
  have hmin : j - i ≤ p.walk.length - i := Nat.sub_le_sub_right
    (by rw [p.length_eq_b, earlier.distance]; exact hj) i
  simpa only [SimpleGraph.Walk.take_length, SimpleGraph.Walk.drop_length,
    inf_eq_left.mpr hmin, SimpleGraph.Walk.drop_getVert, Nat.add_sub_of_le hij] using hh.symm

private theorem window_color (earlier : Earlier R geometry)
    {a f : Vertex R} (p : CriticalPath R geometry a f)
    {i : ℕ} (hi : Even i) (hi8 : i ≤ 8) : color R (p.walk.getVert i) = false :=
  (p.vertex_color (by rw [p.length_eq_b, earlier.distance]; exact hi8)).mpr hi

private theorem window_adjacent (earlier : Earlier R geometry)
    {a f : Vertex R} (p : CriticalPath R geometry a f)
    {i : ℕ} (hi : i < 8) : Adjacent R (p.walk.getVert i) (p.walk.getVert (i + 1)) :=
  (cosetGraph_adj R _ _).mp (p.walk.adj_getVert_succ
    (by rw [p.length_eq_b, earlier.distance]; exact hi))

private structure WindowChoice {a f : Vertex R} (p : CriticalPath R geometry a f) where
  g : FreeAmalgam R
  mem : g ∈ stabilizer R a
  critical : CriticalPath R geometry (act R g (p.walk.getVert 2)) (p.walk.getVert 6)

private abbrev WindowChoice.beta {a f : Vertex R} {p : CriticalPath R geometry a f}
    (s : WindowChoice p) := act R s.g (p.walk.getVert 1)
private abbrev WindowChoice.delta {a f : Vertex R} {p : CriticalPath R geometry a f}
    (s : WindowChoice p) := act R s.g (p.walk.getVert 2)

private theorem window_choices [Finite M] (common : CommonFacts R source geometry)
    (earlier : Earlier R geometry) {a f : Vertex R} (p : CriticalPath R geometry a f)
    (hp : HasTurnConjugators R p) :
    ∃ s₁ s₂ : WindowChoice p,
      (edgeCommutator R a s₁.beta ⊓ edgeCommutator R a s₂.beta) ⊓ Q R f = ⊥ := by
  have ht : Adjacent R a (p.walk.getVert 1) := by
    simpa only [SimpleGraph.Walk.getVert_zero] using window_adjacent earlier p (i := 0) (by decide)
  obtain ⟨t₁, t₂, ht₁, ht₂, _, _, hn₁, hn₂, hsep⟩ :=
    ProductSource.ChoiceConstruction.incident_choices common p ht
  have make (t : Vertex R) (ht : Adjacent R a t)
      (hn : ¬ Z R f ≤ stabilizer R a ⊓
        normalizer (edgeCommutator R a t : Set (FreeAmalgam R))) :
      ∃ s : WindowChoice p, edgeCommutator R a s.beta = edgeCommutator R a t := by
    obtain ⟨g, hg, he, ⟨q⟩⟩ := PrescribedReplacement.exists_critical_path (R := R) (p := p)
      (earlier.replacement _ _ p hp) (by rw [earlier.distance]; decide) ht hn
    have hq : CriticalPath R geometry (act R g (p.walk.getVert 2)) (p.walk.getVert 6) := by
      simpa only [p.length_eq_b, earlier.distance, Nat.reduceSub] using q
    refine ⟨⟨g, hg, hq⟩, ?_⟩
    change edgeCommutator R a (act R g (p.walk.getVert 1)) = _
    have h := RegularPaths.edgeCommutator_act g a (p.walk.getVert 1)
    rw [show act R g a = a from hg] at h
    exact h.trans he
  obtain ⟨s₁, hs₁⟩ := make t₁ ht₁ hn₁
  obtain ⟨s₂, hs₂⟩ := make t₂ ht₂ hn₂
  exact ⟨s₁, s₂, by rw [hs₁, hs₂]; exact hsep⟩

namespace WindowChoice
variable {a f : Vertex R} {p : CriticalPath R geometry a f} (s : WindowChoice p)
include s

private theorem distance (earlier : Earlier R geometry) :
    (cosetGraph R).dist a s.delta = 2 := by
  have h := dist_act R s.g a (p.walk.getVert 2)
  rw [show act R s.g a = a from s.mem] at h
  exact h.trans (p.dist_start (by rw [p.length_eq_b, earlier.distance]; decide))

private theorem adjacent_center (earlier : Earlier R geometry) : Adjacent R a s.beta := by
  have h := (adjacent_act_iff R s.g _ _).mpr
    (window_adjacent earlier p (i := 0) (by decide))
  simpa only [SimpleGraph.Walk.getVert_zero, show act R s.g a = a from s.mem] using h

private theorem adjacent_delta (earlier : Earlier R geometry) : Adjacent R s.beta s.delta :=
  (adjacent_act_iff R s.g _ _).mpr (window_adjacent earlier p (i := 1) (by decide))

private theorem terminal_distance (earlier : Earlier R geometry) :
    (cosetGraph R).dist s.delta (p.walk.getVert 4) = 6 := by
  have hu := (cosetGraph_connected R).dist_triangle (u := s.delta) (v := a)
    (w := p.walk.getVert 4)
  rw [SimpleGraph.dist_comm (u := s.delta) (v := a), s.distance earlier,
    p.dist_start (by rw [p.length_eq_b, earlier.distance]; decide)] at hu
  have hl := (cosetGraph_connected R).dist_triangle (u := s.delta)
    (v := p.walk.getVert 4) (w := p.walk.getVert 6)
  rw [s.critical.shortest.symm.trans s.critical.length_eq_b, earlier.distance,
    window_distance earlier p (by decide) (by decide)] at hl
  omega

private theorem center_moving [Finite M] (common : CommonFacts R source geometry)
    (earlier : Earlier R geometry) : a ∈ Escape.movingNeighbors geometry s.delta := by
  have hl : p.walk.length = 8 := p.length_eq_b.trans earlier.distance
  have hc := window_color earlier p (i := 2) (by decide) (by decide)
  have hm : a ∈ Escape.movingNeighbors geometry (p.walk.getVert 2) := by
    have hr := common.critical_reverse _ p.start_color _ p.end_color p.critical
    apply Escape.Propagation.RadiusFour.Forward.Reversal.critical_endpoint_moving
      source common.large_distance p.end_color hr
    constructor
    · rw [SimpleGraph.dist_comm, p.dist_start (by omega)]
    · rw [SimpleGraph.dist_comm (u := f), p.dist_end,
        SimpleGraph.dist_comm (u := f), ← p.shortest, hl]
  have h := (Escape.PairingControl.FirstPairing.movingNeighbors_act_iff
    common.large_distance s.g (p.walk.getVert 2) a hc).mpr hm
  simpa only [show act R s.g a = a from s.mem] using h

private theorem commutator_ne_bot [Finite M] (common : CommonFacts R source geometry)
    (earlier : Earlier R geometry) :
    ⁅localZSpan R a s.delta, Z R (p.walk.getVert 4)⁆ ≠ ⊥ := by
  have ha := p.start_color
  have hd : color R s.delta = false := s.critical.start_color
  have ht := window_color earlier p (i := 4) (by decide) (by decide)
  have hpred := adjacent_symm R (window_adjacent earlier p (i := 3) (by decide))
  have hl : p.walk.length = 8 := p.length_eq_b.trans earlier.distance
  have hspanQ : localZSpan R a s.delta ≤ Q R (p.walk.getVert 3) := by
    apply (localZSpan_le_V R (s.distance earlier).le).trans
    apply V_le_Q_of_dist_add_two_lt R hd
    have htri := (cosetGraph_connected R).dist_triangle (u := s.delta) (v := a)
      (w := p.walk.getVert 3)
    rw [SimpleGraph.dist_comm (u := s.delta) (v := a), s.distance earlier,
      p.dist_start (by omega)] at htri
    rw [earlier.distance]
    omega
  intro hzero
  have hspan : localZSpan R a s.delta ≤ Q R (p.walk.getVert 4) := by
    rw [← common.centralizer _ _ ht hpred]
    exact le_inf hspanQ (commutator_eq_bot_iff_le_centralizer.mp hzero)
  obtain ⟨n⟩ := earlier.natural_section s.delta hd
  have hm : Vcirc R s.delta ≤ localZSpan R a s.delta := by
    rw [localZSpan_eq_conjugates]
    exact Escape.Initial.Natural.moving_generation_of_naturalSection
      source geometry common.large_distance s.delta hd n a (s.center_moving common earlier)
  have hedge : V R s.beta ≤ Q R (p.walk.getVert 4) := by
    apply (Escape.Initial.Consequences.edge_radius_le_radius ha (s.adjacent_center earlier)).trans
    apply V_le_Q_of_dist_add_two_lt R ha
    rw [p.dist_start (by omega), earlier.distance]
    decide
  apply common.escape s.delta hd _ s.critical.critical (p.walk.getVert 4)
  · rw [window_distance earlier p (by decide) (by decide)]
  · rw [s.critical.shortest.symm.trans s.critical.length_eq_b, earlier.distance,
      s.terminal_distance earlier]
  · rw [Escape.Initial.Consequences.radius_eq_moving_sup_edge source hd
      (adjacent_symm R (s.adjacent_delta earlier))]
    exact sup_le (hm.trans hspan) hedge

private theorem commutator_le_edge [Finite M] (common : CommonFacts R source geometry)
    (earlier : Earlier R geometry) :
    ⁅localZSpan R a s.delta, Z R (p.walk.getVert 4)⁆ ≤ edgeCommutator R a s.beta := by
  have ht := window_color earlier p (i := 4) (by decide) (by decide)
  have hQa : Z R (p.walk.getVert 4) ≤ Q R a := by
    apply Z_le_Q_of_dist_lt R _ (geometry.exists_critical _ ht)
    rw [geometry.distance_constant _ ht, SimpleGraph.dist_comm,
      p.dist_start (by rw [p.length_eq_b, earlier.distance]; decide)]
    change 4 < geometry.b R
    rw [earlier.distance]; decide
  have hQd : Z R (p.walk.getVert 4) ≤ Q R s.delta := by
    apply Z_le_Q_of_dist_lt R _ (geometry.exists_critical _ ht)
    rw [geometry.distance_constant _ ht, SimpleGraph.dist_comm, s.terminal_distance earlier]
    change 6 < geometry.b R
    rw [earlier.distance]; decide
  exact span_commutator_le_edge source common.large_distance p.start_color s.critical.start_color
    (s.distance earlier) (s.adjacent_center earlier) (adjacent_symm R (s.adjacent_delta earlier))
    (le_inf hQa hQd) ((commutator_mono (localZSpan_le_V R (s.distance earlier).le) hQd).trans
      (radius_displacement_le_fixed earlier s.critical.start_color))

private theorem span_le_hatW (earlier : Earlier R geometry) (hp : HasTurnConjugators R p) :
    localZSpan R a s.delta ≤ hatW R a (p.walk.getVert 2) (p.walk.getVert 4) := by
  apply conjugate_span_le_hatW _ s.mem
  obtain ⟨k, hk, ht⟩ := hp 2 (by decide) (by decide)
    (by rw [p.length_eq_b, earlier.distance]; decide)
  exact ⟨k, hk, by simpa only [Nat.reduceAdd, Nat.reduceSub, SimpleGraph.Walk.getVert_zero] using ht⟩

private theorem commutator_le_terminal_kernel (earlier : Earlier R geometry)
    (hp : HasTurnConjugators R p) :
    ⁅localZSpan R a s.delta, Z R (p.walk.getVert 4)⁆ ≤ Q R f := by
  have hWQ : hatW R a (p.walk.getVert 2) (p.walk.getVert 4) ≤ Q R (p.walk.getVert 3) :=
    hatW_le_edge_kernel earlier p.start_color
      (by rw [SimpleGraph.dist_comm, p.dist_start (by rw [p.length_eq_b, earlier.distance]; decide)])
      (by rw [SimpleGraph.dist_comm, window_distance earlier p (by decide) (by decide)])
      (p.dist_start (by rw [p.length_eq_b, earlier.distance]; decide))
  have hlocal : Q R (p.walk.getVert 3) ≤ stabilizer R (p.walk.getVert 4) := fun _ hx =>
    hx.2 _ (window_adjacent earlier p (i := 3) (by decide))
  have hDZ : ⁅localZSpan R a s.delta, Z R (p.walk.getVert 4)⁆ ≤ Z R (p.walk.getVert 4) := by
    rw [commutator_comm]
    exact le_normalizer_iff_commutator_le_left.mp
      (((s.span_le_hatW earlier hp).trans hWQ).trans (hlocal.trans (Z_normalized R _)))
  apply hDZ.trans
  have ht := window_color earlier p (i := 4) (by decide) (by decide)
  apply Z_le_Q_of_dist_lt R _ (geometry.exists_critical _ ht)
  rw [geometry.distance_constant _ ht, p.dist_end, p.length_eq_b]
  change geometry.b R - 4 < geometry.b R
  rw [earlier.distance]
  decide
end WindowChoice

private theorem four_le_card_of_independent {G : Type*} [Group G]
    (A B K : Subgroup G) [Finite K] (hAK : A ≤ K) (hBK : B ≤ K)
    (hA : A ≠ ⊥) (hB : B ≠ ⊥) (hdis : A ⊓ B = ⊥) : 4 ≤ Nat.card K := by
  let J := A ⊔ B
  have hJK : J ≤ K := sup_le hAK hBK
  let : Finite J := Finite.of_injective (inclusion hJK) (inclusion_injective _)
  let : Finite A := Finite.of_injective (inclusion hAK) (inclusion_injective _)
  have hAJ : A ≤ J := le_sup_left
  have hBJ : B ≤ J := le_sup_right
  have hpos : 1 < Nat.card A := (one_lt_card_iff_ne_bot _).mpr hA
  have hlt : Nat.card A < Nat.card J := by
    by_contra! h
    have heq : A = J := eq_of_le_of_card_ge hAJ h
    apply hB
    apply le_bot_iff.mp
    rw [← hdis]
    exact le_inf (heq ▸ hBJ) le_rfl
  obtain ⟨k, hk⟩ := card_dvd_of_le hAJ
  have hk2 : 2 ≤ k := by
    by_contra! h
    interval_cases k
    · simp only [Nat.mul_zero] at hk; omega
    · simp only [Nat.mul_one] at hk; omega
  have hfour : 4 ≤ Nat.card J := by nlinarith
  exact hfour.trans (card_le_of_le hJK)

/-- The two actual selected displacements force order at least four for the
second hat layer on any supplied regular critical window at b=8. -/
public theorem window_displacement_card_lower [Finite M] (common : CommonFacts R source geometry)
    (earlier : Earlier R geometry) {a f : Vertex R} (p : CriticalPath R geometry a f)
    (hp : HasTurnConjugators R p) :
    4 ≤ Nat.card (⁅hatW R a (p.walk.getVert 2) (p.walk.getVert 4),
      Z R (p.walk.getVert 4)⁆ : Subgroup (FreeAmalgam R)) := by
  let K := ⁅hatW R a (p.walk.getVert 2) (p.walk.getVert 4), Z R (p.walk.getVert 4)⁆
  have ht := window_color earlier p (i := 4) (by decide) (by decide)
  have hWQ : hatW R a (p.walk.getVert 2) (p.walk.getVert 4) ≤ Q R (p.walk.getVert 3) :=
    hatW_le_edge_kernel earlier p.start_color
      (by rw [SimpleGraph.dist_comm, p.dist_start (by rw [p.length_eq_b, earlier.distance]; decide)])
      (by rw [SimpleGraph.dist_comm, window_distance earlier p (by decide) (by decide)])
      (p.dist_start (by rw [p.length_eq_b, earlier.distance]; decide))
  have hlocal : Q R (p.walk.getVert 3) ≤ stabilizer R (p.walk.getVert 4) := fun _ hx =>
    hx.2 _ (window_adjacent earlier p (i := 3) (by decide))
  have hKZ : K ≤ Z R (p.walk.getVert 4) := by
    change ⁅hatW R a (p.walk.getVert 2) (p.walk.getVert 4), Z R (p.walk.getVert 4)⁆ ≤ _
    rw [commutator_comm]
    exact le_normalizer_iff_commutator_le_left.mp (hWQ.trans (hlocal.trans (Z_normalized R _)))
  let := finite_stabilizer R (p.walk.getVert 4)
  let : Finite K := Finite.of_injective (inclusion (hKZ.trans (Z_le_stabilizer R _)))
    (inclusion_injective _)
  obtain ⟨s₁, s₂, hsep⟩ := window_choices common earlier p hp
  apply four_le_card_of_independent
    ⁅localZSpan R a s₁.delta, Z R (p.walk.getVert 4)⁆
    ⁅localZSpan R a s₂.delta, Z R (p.walk.getVert 4)⁆ K
    (commutator_mono (s₁.span_le_hatW earlier hp) le_rfl)
    (commutator_mono (s₂.span_le_hatW earlier hp) le_rfl)
    (s₁.commutator_ne_bot common earlier) (s₂.commutator_ne_bot common earlier)
  apply le_bot_iff.mp
  rw [← hsep]
  exact le_inf
    (le_inf (inf_le_left.trans (s₁.commutator_le_edge common earlier))
      (inf_le_right.trans (s₂.commutator_le_edge common earlier)))
    (inf_le_left.trans (s₁.commutator_le_terminal_kernel earlier hp))


/-- The literal second-layer product on the supplied regular critical
window. Selection retains the start and the vertices at offsets two and four. -/
public theorem window_hatW_product [Finite M] (common : CommonFacts R source geometry)
    (earlier : Earlier R geometry) {a f : Vertex R} (p : CriticalPath R geometry a f)
    (hp : HasTurnConjugators R p) :
    (hatW R a (p.walk.getVert 2) (p.walk.getVert 4) : Set (FreeAmalgam R)) *
      (Q R (p.walk.getVert 4) : Set (FreeAmalgam R)) =
        (Q R (p.walk.getVert 3) : Set (FreeAmalgam R)) := by
  apply hatW_product_of_displacement_lower common earlier p.start_color
    (window_color earlier p (i := 4) (by decide) (by decide))
    (adjacent_symm R (window_adjacent earlier p (i := 3) (by decide)))
  · rw [SimpleGraph.dist_comm, p.dist_start (by rw [p.length_eq_b, earlier.distance]; decide)]
  · rw [SimpleGraph.dist_comm, window_distance earlier p (by decide) (by decide)]
  · exact p.dist_start (by rw [p.length_eq_b, earlier.distance]; decide)
  · exact window_displacement_card_lower common earlier p hp

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.CoreFactors.Early.First.Layer
