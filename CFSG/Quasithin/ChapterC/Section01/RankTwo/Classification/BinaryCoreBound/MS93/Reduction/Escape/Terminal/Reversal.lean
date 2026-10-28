module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.Terminal.Orbit
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.Terminal.Geometry

/-!
# Reversing the final critical pairs in MS93 (4.3)

A shortest walk supplies the actual second predecessor for each reversed
critical pair. The width-four application proves the symmetric kernel join
used in the normality argument. At width six, the third displacement and
uniform centrality at six force the selected nonzero critical commutator
into R₀ intersected with the original starting local center, which is trivial.
The third noncommutation premise is supplied by Terminal.Normality.

Source: Meierfrankenfeld--Stellmacher (1993), printed p.890.
-/

public section

namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.Terminal
open Subgroup Stellmacher.PushingUp.AmalgamGraph
open Propagation Propagation.RadiusFour
variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M} {geometry : Geometry R}

omit [Finite M] in
/-- The actual second vertex of a shortest walk of length n+2. -/
theorem exists_second_vertex {x a : Vertex R} {n : ℕ}
    (hxa : (cosetGraph R).dist x a = n + 2) :
    ∃ y, (cosetGraph R).dist x y = 2 ∧ (cosetGraph R).dist y a = n := by
  obtain ⟨w, hw⟩ := (cosetGraph_connected R).exists_walk_length_eq_dist x a
  have hlen : w.length = n + 2 := hw.trans hxa
  have ht := SimpleGraph.length_eq_dist_of_subwalk hw (w.isSubwalk_take 2)
  have hd := SimpleGraph.length_eq_dist_of_subwalk hw (w.isSubwalk_drop 2)
  refine ⟨w.getVert 2, ?_, ?_⟩
  · simpa only [SimpleGraph.Walk.take_length, hlen, Nat.min_eq_left (by omega : 2 ≤ n + 2)] using ht.symm
  · simpa only [SimpleGraph.Walk.drop_length, hlen, Nat.add_sub_cancel] using hd.symm

/-- Reversal with the actual second predecessor, for arbitrary even width. -/
theorem exists_reversed_counterexample (source : LocalSource L R)
    {a l x y : Vertex R} {n : ℕ} (hl : color R l = false) (hx : color R x = false)
    (hcrit : CriticalPair R x l (geometry.exists_critical x hx))
    (hxa : (cosetGraph R).dist x a = n + 2)
    (hal : (cosetGraph R).dist a l + (n + 2) = geometry.b R)
    (hxy : (cosetGraph R).dist x y = 2) (hya : (cosetGraph R).dist y a = n)
    (htrap : V R l ≤ Q R y) :
    ∃ q : Counterexample geometry, q.a = l ∧ q.a' = x ∧ q.c = y ∧
      Before q.a q.a' a (n + 2) := by
  have hxl : (cosetGraph R).dist x l = geometry.b R :=
    hcrit.1.trans (geometry.distance_constant x hx)
  have hly : (cosetGraph R).dist l y + 2 = geometry.b R := by
    have h₁ := (cosetGraph_connected R).dist_triangle (u := x) (v := y) (w := l)
    have h₂ := (cosetGraph_connected R).dist_triangle (u := y) (v := a) (w := l)
    rw [SimpleGraph.dist_comm (u := y) (v := l)] at h₁ h₂
    omega
  let q : Counterexample geometry := {
    a := l
    a' := x
    c := y
    color_a := hl
    critical := source.critical_reverse geometry x hx l hl hcrit
    before := ⟨by rw [SimpleGraph.dist_comm, hxy], by
      rw [SimpleGraph.dist_comm (u := l) (v := x), hxl]; exact hly⟩
    trapped := htrap
  }
  refine ⟨q, rfl, rfl, rfl, ?_⟩
  change Before l x a (n + 2)
  exact ⟨by rw [SimpleGraph.dist_comm, hxa], by
    rw [SimpleGraph.dist_comm (u := l) (v := a),
      SimpleGraph.dist_comm (u := l) (v := x), hxl]; exact hal⟩

/-- The symmetric radius-four join is obtained from a new, genuinely trapped
critical pair. It is not an unproved exchange of endpoint notation. -/
theorem radius_four_join_symmetric (source : LocalSource L R)
    (hb : 2 < geometry.b R) (propagation : PropagationFacts geometry)
    (p : Counterexample geometry) {d t₅ s : Vertex R}
    (hd : Before p.a p.a' d 4) (h₅ : Before p.a p.a' t₅ 5)
    (hs : Before p.a p.a' s 6) : VBall R p.a 4 ⊔ Q R d = Q R t₅ := by
  have hdc : color R d = false := (hd.color (by decide)).trans p.end_color
  have hsc : color R s = false := (hs.color (by decide)).trans p.end_color
  have hnear : (cosetGraph R).dist p.a d + 4 = geometry.b R := hd.2.trans p.distance_eq_b
  have hn : ⁅VBall R p.a 4, Z R d⁆ ≠ ⊥ := by
    intro hc
    apply (propagation.radius_four p d hd).1
    rw [← source.C_eq_Q geometry.radical_ne_bot d hdc]
    exact le_inf (ball_le_stabilizer p.color_a hnear.le)
      (commutator_eq_bot_iff_le_centralizer.mp hc)
  obtain ⟨x, hx, hxa, had, hcrit⟩ := exists_critical_of_not_commuting p.color_a hdc hnear.le hn
  obtain ⟨y, hxy, hya⟩ := exists_second_vertex (n := 2) hxa
  have hmove := fourth_moving_at_six source hb propagation p hd h₅ hs
  have htrap : V R d ≤ Q R y := by
    apply moving_radius_le_Q propagation p hsc hmove
    have hpath := hs.2
    rw [p.distance_eq_b] at hpath
    have ht := (cosetGraph_connected R).dist_triangle (u := s) (v := p.a) (w := y)
    rw [SimpleGraph.dist_comm (u := s) (v := p.a),
      SimpleGraph.dist_comm (u := p.a) (v := y)] at ht
    omega
  obtain ⟨q, hqa, hqe, _, hbefore⟩ := exists_reversed_counterexample source hdc hx
    hcrit hxa had hxy hya htrap
  have hqt : Before q.a' q.a t₅ 1 := by
    rw [hqa, hqe]
    have htd : (cosetGraph R).dist t₅ d = 1 :=
      SimpleGraph.dist_eq_one_iff_adj.mpr ((cosetGraph_adj R _ _).mpr
        (h₅.adjacent (geometry := geometry) hd))
    have hxl : (cosetGraph R).dist x d = geometry.b R :=
      hcrit.1.trans (geometry.distance_constant x hx)
    have ht := (cosetGraph_connected R).dist_triangle (u := x) (v := p.a) (w := t₅)
    have ht' := (cosetGraph_connected R).dist_triangle (u := x) (v := t₅) (w := d)
    have hpath := h₅.2
    rw [p.distance_eq_b] at hpath
    exact ⟨htd, by omega⟩
  have hj := (propagation.radius_four q p.a hbefore).2.2 t₅ hqt
  simpa only [hqa] using hj

/-- The final width-six reversal kills the critical commutator in the original
R₀ and original starting local center. -/
theorem contradiction_of_third_noncommutation (source : LocalSource L R)
    (hb : 2 < geometry.b R) (modules : ModuleFacts source geometry)
    (initial : ∀ q : Counterexample geometry, Nonempty (InitialFacts q))
    (control : ∀ q : Counterexample geometry, LocalControl q) (edge : EdgeTransfer geometry)
    (propagation : PropagationFacts geometry) (p : Counterexample geometry)
    {d t₃ t₅ s t₇ : Vertex R} (h₇ : Before p.a p.a' t₇ 7)
    (w : ThirdOrbitWitnesses p d t₃ t₅ s t₇)
    (hne : ⁅VBall R p.a 6, Z R w.rho⁆ ≠ ⊥) : False := by
  have hl : color R w.rho = false := by
    rw [← w.image, action_preserves_color]
    exact Forward.lam_color p (centralWitness w.earlier)
  have hnear : (cosetGraph R).dist p.a w.rho + 6 ≤ geometry.b R := by
    have hpath := h₇.2
    rw [p.distance_eq_b] at hpath
    have htl := SimpleGraph.dist_eq_one_iff_adj.mpr ((cosetGraph_adj R _ _).mpr
      (adjacent_symm R w.adjacent))
    have ht := (cosetGraph_connected R).dist_triangle (u := p.a) (v := t₇) (w := w.rho)
    omega
  obtain ⟨x, hx, hxa, hal, hcrit⟩ := exists_critical_of_not_commuting p.color_a hl hnear hne
  obtain ⟨y, hxy, hya⟩ := exists_second_vertex (n := 4) hxa
  obtain ⟨e, he⟩ := p.exists_before (eight_le propagation p)
  have hec : color R e = false := (he.color (by decide)).trans p.end_color
  have hmove := moving_of_ball_noncommutation source hb p h₇ he w.adjacent hl hne
  have htrap : V R w.rho ≤ Q R y := by
    apply moving_radius_le_Q propagation p hec hmove
    have hpath := he.2
    rw [p.distance_eq_b] at hpath
    have ht := (cosetGraph_connected R).dist_triangle (u := e) (v := p.a) (w := y)
    rw [SimpleGraph.dist_comm (u := e) (v := p.a),
      SimpleGraph.dist_comm (u := p.a) (v := y)] at ht
    omega
  obtain ⟨q, hqa, hqe, _, hbefore⟩ := exists_reversed_counterexample source hl hx
    hcrit hxa hal hxy hya htrap
  have hc := radius_central_at_six source hb modules control edge propagation q hbefore
  have hcritcentral : criticalCommutator x w.rho ≤ localCenter p.a := by
    apply le_trans _ hc
    rw [radiusCommutator, hqa, hqe, criticalCommutator, commutator_comm]
    exact commutator_mono (Z_le_VBall R w.rho 2) le_rfl
  have hQ : Z R x ≤ Q R t₇ := by
    apply Z_le_Q_of_dist_lt R x (geometry.exists_critical x hx)
    rw [geometry.distance_constant x hx]
    change (cosetGraph R).dist x t₇ < geometry.b R
    have hpath := h₇.2
    rw [p.distance_eq_b] at hpath
    have ht := (cosetGraph_connected R).dist_triangle (u := x) (v := p.a) (w := t₇)
    omega
  have hR : criticalCommutator x w.rho ≤ radiusCommutator p.a p.a' := by
    rw [w.displacement, criticalCommutator, edgeDisplacement, commutator_comm]
    exact commutator_mono le_rfl hQ
  obtain ⟨hi⟩ := initial p
  have hdis := Forward.Reversal.radius_disjoint source hb modules p hi
  apply source.critical_noncommutation geometry x hx hcrit
  apply le_bot_iff.mp
  rw [← hdis]
  exact le_inf hR hcritcentral

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.Terminal
