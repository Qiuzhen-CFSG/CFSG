module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.Basic
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.Initial.Paths

/-!
# Moving a contrary configuration to a prescribed edge

The amalgam action is transitive on oriented edges of a fixed color. Thus a
contrary critical pair can be transported so that either its first or its
last edge is any prescribed edge. The transported object retains its actual
critical pair, the specified vertex two before the endpoint, and the contrary
containment. This justifies applying the preceding stages of (4.3) at new
vertices without an implicit change of the configuration.

Source: Meierfrankenfeld--Stellmacher (1993), (4.3.3)--(4.3.8), pp.886--889.
-/

public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.Propagation
variable {M : Type*} [Group M] {R : Subgroup M} {geometry : Geometry R}

/-- A transport specification with all three vertex images visible to clients. -/
theorem exists_counterexample_transport (p : Counterexample geometry) (g : FreeAmalgam R) :
    ∃ q : Counterexample geometry,
      q.a = act R g p.a ∧ q.a' = act R g p.a' ∧ q.c = act R g p.c := by
  refine ⟨{
    a := act R g p.a
    a' := act R g p.a'
    c := act R g p.c
    color_a := by rw [action_preserves_color]; exact p.color_a
    critical := (criticalPair_act_iff R g p.a p.a' _ _).mpr p.critical
    before := by simpa only [Before, dist_act] using p.before
    trapped := by rw [V_act, Q_act]; exact map_mono p.trapped
  }, rfl, rfl, rfl⟩

/-- Edge transitivity with the orientation fixed by the M-color. -/
theorem exists_edge_transport {a t d e : Vertex R}
    (ha : color R a = false) (hd : color R d = false)
    (hat : Adjacent R a t) (hde : Adjacent R d e) :
    ∃ g : FreeAmalgam R, act R g a = d ∧ act R g t = e := by
  obtain ⟨g, h | h⟩ := edge_transitive R hat hde
  · exact ⟨g, h⟩
  · have he : color R e = false := by
      rw [← h.1, action_preserves_color, ha]
    exact ((adjacent_color_ne R hde) (hd.trans he.symm)).elim

/-- The first edge of a transported contrary pair can be prescribed. -/
theorem counterexample_at_edge (p : Counterexample geometry)
    (hb : 0 < geometry.b R) (a t : Vertex R)
    (ha : color R a = false) (hat : Adjacent R a t) :
    ∃ q : Counterexample geometry, q.a = a ∧ Before q.a' q.a t 1 := by
  obtain ⟨s, hs, hdist⟩ := exists_adjacent_dist_sub_one R p.a p.a'
    (p.distance_eq_b.symm ▸ hb)
  have hbefore : Before p.a' p.a s 1 := by
    constructor
    · rw [SimpleGraph.dist_comm]
      exact SimpleGraph.dist_eq_one_iff_adj.mpr ((cosetGraph_adj R _ _).mpr hs)
    · simpa only [SimpleGraph.dist_comm] using hdist
  obtain ⟨g, hga, hgs⟩ := exists_edge_transport p.color_a ha hs hat
  obtain ⟨q, hq, hq', _⟩ := exists_counterexample_transport p g
  refine ⟨q, hq.trans hga, ?_⟩
  rw [hq, hq', ← hgs]
  simpa only [Before, dist_act] using hbefore

/-- A contrary configuration exists at every M-vertex if it exists at one. -/
theorem counterexample_at_vertex (p : Counterexample geometry)
    (hb : 0 < geometry.b R) (a : Vertex R) (ha : color R a = false) :
    ∃ q : Counterexample geometry, q.a = a := by
  obtain ⟨g, rfl⟩ := exists_mVertex_of_color R ha
  have hadj := (adjacent_act_iff R g (mVertex R 1) (hVertex R 1)).mpr (base_adjacent R)
  simp only [act_mVertex, act_hVertex, one_mul] at hadj
  obtain ⟨q, hq, _⟩ := counterexample_at_edge p hb _ _ rfl hadj
  exact ⟨q, hq⟩

/-- Global use of the local commutator bound is justified by actual transport. -/
theorem commutator_le_fixed_at (p : Counterexample geometry)
    (hb : 0 < geometry.b R) (control : ∀ q : Counterexample geometry, LocalControl q)
    (a : Vertex R) (ha : color R a = false) : ⁅V R a, Q R a⁆ ≤ fixedCore R a := by
  obtain ⟨q, hqa⟩ := counterexample_at_vertex p hb a ha
  simpa only [hqa] using (control q).commutator_le_fixed

/-- The two edge equalities of (4.3.2) at an arbitrary oriented edge. -/
theorem moving_edge_eq_at (p : Counterexample geometry)
    (hb : 0 < geometry.b R) (control : ∀ q : Counterexample geometry, LocalControl q)
    (a t d : Vertex R) (ha : color R a = false) (hat : Adjacent R a t)
    (hdt : Adjacent R d t) (hd : d ∈ movingNeighbors geometry a) :
    H R a = ⁅Z R d, Q R a⁆ ∧ H R a = edgeDisplacement d t := by
  obtain ⟨q, hqa, hqt⟩ := counterexample_at_edge p hb a t ha hat
  have hqd : d ∈ movingNeighbors geometry q.a := by simpa only [hqa] using hd
  simpa only [hqa] using (control q).H_eq_edge t hqt d hdt hqd

variable [Finite M]

/-- The last edge can also be prescribed; this transfers the R₀ order
calculation to every edge displacement. -/
theorem counterexample_ending_at_edge (p : Counterexample geometry)
    (hb : 0 < geometry.b R) (a t : Vertex R)
    (ha : color R a = false) (hat : Adjacent R a t) :
    ∃ q : Counterexample geometry, q.a' = a ∧ Before q.a q.a' t 1 := by
  obtain ⟨s, hs⟩ := p.exists_before (show 1 ≤ geometry.b R by omega)
  obtain ⟨g, hga, hgs⟩ := exists_edge_transport p.end_color ha hs.endpoint_adjacent hat
  obtain ⟨q, hq, hq', _⟩ := exists_counterexample_transport p g
  refine ⟨q, hq'.trans hga, ?_⟩
  rw [hq, hq', ← hgs]
  simpa only [Before, dist_act] using hs

/-- (4.3.1)(i) gives order four at every oriented edge, using a genuine
translate of the original contrary configuration. -/
theorem edge_card (p : Counterexample geometry) (hb : 0 < geometry.b R)
    (initial : ∀ q : Counterexample geometry, Nonempty (InitialFacts q))
    (a t : Vertex R) (ha : color R a = false) (hat : Adjacent R a t) :
    Nat.card (edgeDisplacement a t) = 4 := by
  obtain ⟨q, hqa, hqt⟩ := counterexample_ending_at_edge p hb a t ha hat
  obtain ⟨hq⟩ := initial q
  have h := hq.radius_eq_edge t hqt
  rw [hqa] at h
  rw [← h]
  simpa only [hqa] using hq.radius_card

/-- Actual local conjugators with the geometric properties used to choose
μ and λ in (4.3.8). The displacement and intersection identities require
the later centrality argument and are not asserted here. -/
theorem local_orbit_choices (p : Counterexample geometry) (d t₃ t₅ : Vertex R)
    (hd : Before p.a p.a' d 4) (h₃ : Before p.a p.a' t₃ 3)
    (h₅ : Before p.a p.a' t₅ 5) :
    ∃ g ∈ stabilizer R p.c, ∃ h ∈ stabilizer R d,
      Adjacent R (act R g p.a') t₃ ∧ Adjacent R (act R h (act R g p.a')) t₅ := by
  have hb : 1 ≤ geometry.b R := by
    have hh := h₅.2
    rw [p.distance_eq_b] at hh
    omega
  obtain ⟨s, hs⟩ := p.exists_before hb
  have hcs : Adjacent R p.c s := p.before.adjacent (geometry := geometry) hs
  have hc₃ : Adjacent R p.c t₃ :=
    adjacent_symm R (h₃.adjacent (geometry := geometry) p.before)
  obtain ⟨g, hg, hgs⟩ := stabilizer_transitive_neighbors R p.c hcs hc₃
  have hμ₃ : Adjacent R (act R g p.a') t₃ := by
    rw [← hgs]
    exact (adjacent_act_iff R g _ _).mpr hs.endpoint_adjacent
  have hd₃ : Adjacent R d t₃ := hd.adjacent (geometry := geometry) h₃
  have hd₅ : Adjacent R d t₅ := adjacent_symm R (h₅.adjacent (geometry := geometry) hd)
  obtain ⟨h, hh, hh₃⟩ := stabilizer_transitive_neighbors R d hd₃ hd₅
  refine ⟨g, hg, h, hh, hμ₃, ?_⟩
  rw [← hh₃]
  exact (adjacent_act_iff R h _ _).mpr hμ₃

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.Propagation
