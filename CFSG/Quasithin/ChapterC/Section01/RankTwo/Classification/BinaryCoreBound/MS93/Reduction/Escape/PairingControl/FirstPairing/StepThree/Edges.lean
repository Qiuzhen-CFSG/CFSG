module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.PairingControl.FirstPairing.Source
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.PairingControl.FirstPairing.Transport

/-!
# Critical configurations at arbitrary edges in MS93 (4.3.2)(3)

Transport all three vertices of the contrary configuration by an actual
amalgam element. Edge transitivity then puts its first or last edge at any
prescribed oriented edge. The first transport preserves the contrary
commutator assumption as well as the critical pair and trapped V-layer.

Applying InitialFacts to these entire translated configurations identifies
[Z_delta,Q_alpha] with the delta-side displacement and gives order four for
every edge displacement. No later escape or LocalControl result is used.
These statements do not identify the alpha-side displacement; that is the
rank-one argument still required in step (3).

The transport proofs adapt the elementary geometry in
Escape/Propagation/Transport.lean, without importing its later interfaces.
Source: Meierfrankenfeld--Stellmacher (1993), (4.3.1)(i),(vii) and
(4.3.2)(3), printed pp.883--884.
-/

public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.PairingControl.FirstPairing.StepThree
variable {M : Type*} [Group M] {L R : Subgroup M} {geometry : Geometry R}

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

theorem exists_oriented_edge_transport {a t d e : Vertex R}
    (ha : color R a = false) (hd : color R d = false)
    (hat : Adjacent R a t) (hde : Adjacent R d e) :
    ∃ g : FreeAmalgam R, act R g a = d ∧ act R g t = e := by
  obtain ⟨g, h | h⟩ := edge_transitive R hat hde
  · exact ⟨g, h⟩
  · have he : color R e = false := by
      rw [← h.1, action_preserves_color, ha]
    exact ((adjacent_color_ne R hde) (hd.trans he.symm)).elim

theorem contrary_at_edge (p : Counterexample geometry)
    (hb : 0 < geometry.b R) (bad : ¬ ⁅V R p.a, Q R p.a⁆ ≤ fixedCore R p.a)
    (a t : Vertex R) (ha : color R a = false) (hat : Adjacent R a t) :
    ∃ q : Counterexample geometry, q.a = a ∧ Before q.a' q.a t 1 ∧
      ¬ ⁅V R q.a, Q R q.a⁆ ≤ fixedCore R q.a := by
  obtain ⟨s, hs, hdist⟩ := exists_adjacent_dist_sub_one R p.a p.a'
    (p.distance_eq_b.symm ▸ hb)
  have hbefore : Before p.a' p.a s 1 := by
    constructor
    · rw [SimpleGraph.dist_comm]
      exact SimpleGraph.dist_eq_one_iff_adj.mpr ((cosetGraph_adj R _ _).mpr hs)
    · simpa only [SimpleGraph.dist_comm] using hdist
  obtain ⟨g, hga, hgs⟩ := exists_oriented_edge_transport p.color_a ha hs hat
  obtain ⟨q, hq, hq', _⟩ := exists_counterexample_transport p g
  refine ⟨q, hq.trans hga, ?_, ?_⟩
  · rw [hq, hq', ← hgs]
    simpa only [Before, dist_act] using hbefore
  · rw [hq]
    exact (bad_act_iff g p.a).mpr bad

theorem moving_commutator_eq_edge_at (p : Counterexample geometry)
    (hb : 0 < geometry.b R)
    (initial : ∀ q : Counterexample geometry, Nonempty (InitialFacts q))
    (bad : ¬ ⁅V R p.a, Q R p.a⁆ ≤ fixedCore R p.a)
    (a t d : Vertex R) (ha : color R a = false) (hat : Adjacent R a t)
    (hdt : Adjacent R d t) (hd : d ∈ movingNeighbors geometry a) :
    ⁅Z R d, Q R a⁆ = edgeDisplacement d t := by
  obtain ⟨q, hqa, hqt, _⟩ := contrary_at_edge p hb bad a t ha hat
  obtain ⟨hq⟩ := initial q
  have hqd : d ∈ movingNeighbors geometry q.a := hqa.symm ▸ hd
  simpa only [hqa] using hq.edge_commutator t hqt d hdt hqd

variable [Finite M]

theorem counterexample_ending_at_edge (p : Counterexample geometry)
    (hb : 0 < geometry.b R) (a t : Vertex R)
    (ha : color R a = false) (hat : Adjacent R a t) :
    ∃ q : Counterexample geometry, q.a' = a ∧ Before q.a q.a' t 1 := by
  obtain ⟨s, hs⟩ := p.exists_before (show 1 ≤ geometry.b R by omega)
  obtain ⟨g, hga, hgs⟩ := exists_oriented_edge_transport p.end_color ha hs.endpoint_adjacent hat
  obtain ⟨q, hq, hq', _⟩ := exists_counterexample_transport p g
  refine ⟨q, hq'.trans hga, ?_⟩
  rw [hq, hq', ← hgs]
  simpa only [Before, dist_act] using hs

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

theorem moving_commutator_card_at (p : Counterexample geometry)
    (hb : 0 < geometry.b R)
    (initial : ∀ q : Counterexample geometry, Nonempty (InitialFacts q))
    (bad : ¬ ⁅V R p.a, Q R p.a⁆ ≤ fixedCore R p.a)
    (a t d : Vertex R) (ha : color R a = false) (hat : Adjacent R a t)
    (hdt : Adjacent R d t) (hd : d ∈ movingNeighbors geometry a) :
    Nat.card (⁅Z R d, Q R a⁆ : Subgroup (FreeAmalgam R)) = 4 := by
  rw [moving_commutator_eq_edge_at p hb initial bad a t d ha hat hdt hd]
  exact edge_card p hb initial d t (moving_color ha hd) hdt

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.PairingControl.FirstPairing.StepThree
