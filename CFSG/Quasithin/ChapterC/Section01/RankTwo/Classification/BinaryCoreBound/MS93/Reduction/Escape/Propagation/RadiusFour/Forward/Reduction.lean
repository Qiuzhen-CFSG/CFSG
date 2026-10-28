module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.Propagation.RadiusFour.Forward.Geometry

/-!
# The reversed critical configuration in MS93 (4.3.8)

The selected critical pair is reversed with its actual midpoint and trapping
bound. Centrality at its fourth predecessor puts its critical commutator in
the original local center, while the prescribed lambda-edge puts it in R₀.
Thus R₀ intersecting that center trivially gives the source contradiction.

The last two product deductions use actual transported counterexamples before
applying BackwardFacts. The selected movement and central intersection needed
to apply the contradiction remain separate targets in Forward.Stages.

Source: Meierfrankenfeld--Stellmacher (1993), first three paragraphs of
(4.3.8), printed p.889, before the final contradiction for (4.3).
-/

public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.Propagation.RadiusFour.Forward
variable {M : Type*} [Group M] {R : Subgroup M} {geometry : Geometry R}
variable [Finite M] {L : Subgroup M}

/-- The reversed contrary configuration retains its midpoint and both exact
geodesic equations. The only additional premise is its actual trapping bound. -/
theorem exists_reversed_counterexample (source : LocalSource L R)
    (p : Counterexample geometry) {d t₃ t₅ : Vertex R}
    (w : CentralOrbitWitnesses p d t₃ t₅) (x y : Vertex R)
    (hx : color R x = false)
    (hcrit : CriticalPair R x w.lam (geometry.exists_critical x hx))
    (hxa : (cosetGraph R).dist x p.a = 4)
    (hal : (cosetGraph R).dist p.a w.lam + 4 = geometry.b R)
    (hxy : (cosetGraph R).dist x y = 2)
    (hya : (cosetGraph R).dist y p.a = 2)
    (htrap : V R w.lam ≤ Q R y) :
    ∃ q : Counterexample geometry, q.a = w.lam ∧ q.a' = x ∧ q.c = y ∧
      Before q.a q.a' p.a 4 := by
  have hxl : (cosetGraph R).dist x w.lam = geometry.b R :=
    hcrit.1.trans (geometry.distance_constant x hx)
  have hly : (cosetGraph R).dist w.lam y + 2 = geometry.b R := by
    have h₁ := (cosetGraph_connected R).dist_triangle (u := x) (v := y) (w := w.lam)
    have h₂ := (cosetGraph_connected R).dist_triangle (u := y) (v := p.a) (w := w.lam)
    rw [SimpleGraph.dist_comm (u := y) (v := w.lam)] at h₁ h₂
    omega
  let q : Counterexample geometry := {
    a := w.lam
    a' := x
    c := y
    color_a := lam_color p w
    critical := source.critical_reverse geometry x hx w.lam (lam_color p w) hcrit
    before := ⟨by rw [SimpleGraph.dist_comm, hxy], by
      rw [SimpleGraph.dist_comm (u := w.lam) (v := x), hxl]; exact hly⟩
    trapped := htrap
  }
  refine ⟨q, rfl, rfl, rfl, ?_⟩
  change Before w.lam x p.a 4
  exact ⟨by rw [SimpleGraph.dist_comm, hxa], by
    rw [SimpleGraph.dist_comm (u := w.lam) (v := p.a),
      SimpleGraph.dist_comm (u := w.lam) (v := x), hxl]; exact hal⟩

omit [Finite M] in
/-- The critical displacement selected on the backwards extension lies in
R₀, using the specified edge of the second actual conjugate. -/
theorem selected_commutator_le_radius (p : Counterexample geometry)
    {d t₃ t₅ : Vertex R} (h₅ : Before p.a p.a' t₅ 5)
    (w : CentralOrbitWitnesses p d t₃ t₅) (x : Vertex R)
    (hx : color R x = false) (hxa : (cosetGraph R).dist x p.a = 4) :
    criticalCommutator x w.lam ≤ radiusCommutator p.a p.a' := by
  have hQ : Z R x ≤ Q R t₅ := by
    apply Z_le_Q_of_dist_lt R x (geometry.exists_critical x hx)
    rw [geometry.distance_constant x hx]
    change (cosetGraph R).dist x t₅ < geometry.b R
    have hpath := h₅.2
    rw [p.distance_eq_b] at hpath
    have htri := (cosetGraph_connected R).dist_triangle (u := x) (v := p.a) (w := t₅)
    omega
  rw [w.second_displacement, criticalCommutator, edgeDisplacement, commutator_comm]
  exact commutator_mono le_rfl hQ

/-- Once the reversed pair is trapped, already proved centrality kills its
nonzero critical commutator against R₀ ∩ Z(G_alpha). -/
theorem selected_contradiction (source : LocalSource L R)
    (hb : 0 < geometry.b R) (backward : BackwardFacts geometry)
    (p : Counterexample geometry) {d t₃ t₅ : Vertex R}
    (h₅ : Before p.a p.a' t₅ 5) (w : CentralOrbitWitnesses p d t₃ t₅)
    (hdisjoint : radiusCommutator p.a p.a' ⊓ localCenter p.a = ⊥)
    (x y : Vertex R) (hx : color R x = false)
    (hcrit : CriticalPair R x w.lam (geometry.exists_critical x hx))
    (hxa : (cosetGraph R).dist x p.a = 4)
    (hal : (cosetGraph R).dist p.a w.lam + 4 = geometry.b R)
    (hxy : (cosetGraph R).dist x y = 2)
    (hya : (cosetGraph R).dist y p.a = 2)
    (htrap : V R w.lam ≤ Q R y) : False := by
  obtain ⟨q, hqa, hqe, hqc, hbefore⟩ :=
    exists_reversed_counterexample source p w x y hx hcrit hxa hal hxy hya htrap
  have hcentral := radius_central_at_four hb backward q p.a hbefore
  have hcritcentral : criticalCommutator x w.lam ≤ localCenter p.a := by
    apply le_trans _ hcentral
    rw [radiusCommutator, hqa, hqe, criticalCommutator, commutator_comm]
    exact commutator_mono (Z_le_VBall R w.lam 2) le_rfl
  apply source.critical_noncommutation geometry x hx hcrit
  apply le_bot_iff.mp
  rw [← hdisjoint]
  exact le_inf (selected_commutator_le_radius p h₅ w x hx hxa) hcritcentral

/-- The source's last nonmoving deduction reduces to its preceding
noncontainment, with the local product and its distance bound proved here. -/
theorem nonmoving_of_not_le (hb : 4 < geometry.b R) (backward : BackwardFacts geometry)
    (p : Counterexample geometry) {d t₃ t₅ : Vertex R}
    (hd : Before p.a p.a' d 4) (w : CentralOrbitWitnesses p d t₃ t₅)
    (hnot : ¬ V R w.mu ≤ Q R p.a) : w.mu ∉ movingNeighbors geometry d := by
  intro hmove
  have hdcol : color R d = false := (hd.color (by decide)).trans p.end_color
  obtain ⟨q, hqa⟩ := counterexample_at_vertex p (by omega) d hdcol
  have hsym := backward.moving_symmetric q w.mu
  rw [hqa] at hsym
  have hh := backward.product_normal q w.mu (by simpa only [hqa] using hmove.1)
    (by simpa only [hqa] using hsym.mp hmove)
  rw [hqa] at hh
  have hnear : (cosetGraph R).dist d p.a + 2 < geometry.b R := by
    have hpath := hd.2
    rw [p.distance_eq_b, SimpleGraph.dist_comm (u := p.a) (v := d)] at hpath
    omega
  exact hnot (le_sup_left.trans (normal_product_le_Q hdcol hb hmove.1 hh.1 hh.2.1 hnear))


/-- The moving-neighbor product at alpha'-6 supplies exactly the trapping
bound needed at the midpoint of the selected backwards extension. -/
theorem selected_trapped_of_moving (hb : 4 < geometry.b R)
    (backward : BackwardFacts geometry) (p : Counterexample geometry)
    {s l y : Vertex R} (hs : Before p.a p.a' s 6)
    (hmove : l ∈ movingNeighbors geometry s)
    (hya : (cosetGraph R).dist y p.a ≤ 2) : V R l ≤ Q R y := by
  have hscol : color R s = false := (hs.color (by decide)).trans p.end_color
  obtain ⟨q, hqa⟩ := counterexample_at_vertex p (by omega) s hscol
  have hsym := backward.moving_symmetric q l
  rw [hqa] at hsym
  have hh := backward.product_normal q l (by simpa only [hqa] using hmove.1)
    (by simpa only [hqa] using hsym.mp hmove)
  rw [hqa] at hh
  have hnear : (cosetGraph R).dist s y + 2 < geometry.b R := by
    have hpath := hs.2
    rw [p.distance_eq_b, SimpleGraph.dist_comm (u := p.a) (v := s)] at hpath
    have htri := (cosetGraph_connected R).dist_triangle (u := s) (v := p.a) (w := y)
    rw [SimpleGraph.dist_comm (u := p.a) (v := y)] at htri
    omega
  exact le_sup_left.trans (normal_product_le_Q hscol hb hmove.1 hh.1 hh.2.1 hnear)


omit [Finite M] in
/-- The original sixth predecessor is the actual second predecessor of
lambda in the selected critical pair, not an unrelated distance-two vertex. -/
theorem selected_six_before (p : Counterexample geometry)
    {d t₃ t₅ s : Vertex R} (h₅ : Before p.a p.a' t₅ 5)
    (hs : Before p.a p.a' s 6) (w : CentralOrbitWitnesses p d t₃ t₅)
    {x : Vertex R} (hx : color R x = false)
    (hcrit : CriticalPair R x w.lam (geometry.exists_critical x hx))
    (hxa : (cosetGraph R).dist x p.a = 4)
    (hal : (cosetGraph R).dist p.a w.lam + 4 = geometry.b R) :
    Before x w.lam s 2 := by
  have hs₅ : Adjacent R s t₅ := hs.adjacent (geometry := geometry) h₅
  have hdist₁ : (cosetGraph R).dist s t₅ = 1 :=
    SimpleGraph.dist_eq_one_iff_adj.mpr ((cosetGraph_adj R _ _).mpr hs₅)
  have hdist₂ : (cosetGraph R).dist t₅ w.lam = 1 :=
    SimpleGraph.dist_eq_one_iff_adj.mpr
      ((cosetGraph_adj R _ _).mpr (adjacent_symm R w.second_adjacent))
  have hpath := hs.2
  rw [p.distance_eq_b] at hpath
  have htri₁ := (cosetGraph_connected R).dist_triangle (u := s) (v := t₅) (w := w.lam)
  have htri₂ := (cosetGraph_connected R).dist_triangle (u := p.a) (v := s) (w := w.lam)
  have hsl : (cosetGraph R).dist s w.lam = 2 := by omega
  have hxl : (cosetGraph R).dist x w.lam = geometry.b R :=
    hcrit.1.trans (geometry.distance_constant x hx)
  have htri₃ := (cosetGraph_connected R).dist_triangle (u := x) (v := p.a) (w := s)
  have htri₄ := (cosetGraph_connected R).dist_triangle (u := x) (v := s) (w := w.lam)
  exact ⟨hsl, by omega⟩

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.Propagation.RadiusFour.Forward
