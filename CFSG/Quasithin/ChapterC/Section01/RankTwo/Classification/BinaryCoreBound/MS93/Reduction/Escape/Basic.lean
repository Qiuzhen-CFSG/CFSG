module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.Source
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.SectionThree.CriticalModules.LocalStructure
public import Theory.GroupTheory.ElementaryEightPairing

/-!
# Elementary consequences of a contrary escape configuration

The contrary configuration transports by the actual amalgam action. Its
radius commutator R_0 lies in both V_alpha and Z_alpha', and contains the
nontrivial critical commutator R. All the finite and elementary calculations
are made in these finite local subgroups, never in the infinite amalgam.

In the binary case the existing elementary-eight pairing gives |R| = 2
without an extra image-order assumption. This proves the order assertion in
(4.3.1)(ii); the image order and the remaining assertions of (4.3.1) are
separate obligations.

Source: Meierfrankenfeld--Stellmacher (1993), (2.2), (3.5), and the start
of (4.3), printed pp.856--857, 869--870, 882.
-/

public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape
variable {M : Type*} [Group M] {L R : Subgroup M} {geometry : Geometry R}

theorem Before.endpoint_adjacent {a a' t : Vertex R} (h : Before a a' t 1) :
    Adjacent R a' t := by
  apply adjacent_symm R
  exact (cosetGraph_adj R _ _).mp (SimpleGraph.dist_eq_one_iff_adj.mp h.1)

theorem Before.color {a a' c : Vertex R} {n : ℕ} (h : Before a a' c n)
    (hn : Even n) : color R c = color R a' :=
  color_eq_of_dist_even R c a' (h.1.symm ▸ hn)

namespace Counterexample

theorem distance_eq_b (p : Counterexample geometry) :
    (cosetGraph R).dist p.a p.a' = geometry.b R :=
  p.critical.1.trans (geometry.distance_constant p.a p.color_a)

/-- Choose a genuine shortest walk through the specified vertex two before
the endpoint. This makes the printed alpha+i notation available without a
WLOG identification of different paths or critical pairs. -/
theorem exists_walk (p : Counterexample geometry) :
    ∃ w : (cosetGraph R).Walk p.a p.a',
      w.length = geometry.b R ∧ w.length = (cosetGraph R).dist p.a p.a' ∧
        w.getVert (geometry.b R - 2) = p.c := by
  obtain ⟨u, hu⟩ := (cosetGraph_connected R).exists_walk_length_eq_dist p.a p.c
  obtain ⟨v, hv⟩ := (cosetGraph_connected R).exists_walk_length_eq_dist p.c p.a'
  have hlen : (u.append v).length = (cosetGraph R).dist p.a p.a' := by
    rw [SimpleGraph.Walk.length_append, hu, hv, p.before.1]
    exact p.before.2
  refine ⟨u.append v, hlen.trans p.distance_eq_b, hlen, ?_⟩
  have hprefix : geometry.b R - 2 = u.length := by
    have hpath := p.before.2
    rw [p.distance_eq_b] at hpath
    omega
  simp [hprefix, SimpleGraph.Walk.getVert_append]

/-- A shortest walk supplies every earlier vertex needed by (4.3.6)--(4.3.8),
with the exact two distance equations rather than truncated subtraction alone. -/
theorem exists_before (p : Counterexample geometry) {n : ℕ} (hn : n ≤ geometry.b R) :
    ∃ d, Before p.a p.a' d n := by
  obtain ⟨w, hw, hd, _⟩ := p.exists_walk
  refine ⟨w.getVert (geometry.b R - n), ?_, ?_⟩
  · have h := SimpleGraph.length_eq_dist_of_subwalk hd
      (w.isSubwalk_drop (geometry.b R - n))
    simp only [SimpleGraph.Walk.drop_length, hw] at h
    simpa only [Nat.sub_sub_self hn] using h.symm
  · have h := SimpleGraph.length_eq_dist_of_subwalk hd
      (w.isSubwalk_take (geometry.b R - n))
    simp only [SimpleGraph.Walk.take_length, hw,
      inf_eq_left.mpr (Nat.sub_le (geometry.b R) n)] at h
    rw [← h, p.distance_eq_b]
    exact Nat.sub_add_cancel hn

/-- Translate all three vertices and the contrary subgroup containment. -/
def translate (p : Counterexample geometry) (g : FreeAmalgam R) :
    Counterexample geometry where
  a := act R g p.a
  a' := act R g p.a'
  c := act R g p.c
  color_a := by rw [action_preserves_color]; exact p.color_a
  critical := (criticalPair_act_iff R g p.a p.a' _ _).mpr p.critical
  before := by simpa only [Before, dist_act] using p.before
  trapped := by rw [V_act, Q_act]; exact map_mono p.trapped

variable [Finite M]

theorem end_color (p : Counterexample geometry) : color R p.a' = false :=
  critical_endpoint_color R p.a p.color_a _ p.critical

theorem before_color (p : Counterexample geometry) : color R p.c = false :=
  (p.before.color (by decide)).trans p.end_color

theorem end_Z_le_start_stabilizer (p : Counterexample geometry) :
    Z R p.a' ≤ stabilizer R p.a := by
  apply Z_le_stabilizer_of_dist_le p.a' (geometry.exists_critical p.a' p.end_color)
  rw [SimpleGraph.dist_comm, geometry.distance_constant p.a' p.end_color]
  exact p.distance_eq_b.le

theorem radius_le_start (p : Counterexample geometry) :
    radiusCommutator p.a p.a' ≤ V R p.a :=
  le_normalizer_iff_commutator_le_left.mp
    (p.end_Z_le_start_stabilizer.trans (V_normalized p.a))

theorem radius_le_end (p : Counterexample geometry) :
    radiusCommutator p.a p.a' ≤ Z R p.a' :=
  le_normalizer_iff_commutator_le_right.mp
    ((p.trapped.trans (Q_le_stabilizer_of_dist_two R p.c p.a' p.before_color p.before.1)).trans
      (Z_normalized R p.a'))

theorem radius_le_kernel (p : Counterexample geometry) :
    radiusCommutator p.a p.a' ≤ Q R p.c := p.radius_le_start.trans p.trapped

theorem critical_le_radius_inf_start (p : Counterexample geometry) :
    criticalCommutator p.a p.a' ≤ radiusCommutator p.a p.a' ⊓ Z R p.a :=
  le_inf (commutator_mono (Z_le_VBall R p.a 2) le_rfl)
    (le_normalizer_iff_commutator_le_left.mp
      (p.end_Z_le_start_stabilizer.trans (Z_normalized R p.a)))

theorem radius_ne_bot (p : Counterexample geometry) (source : LocalSource L R) :
    radiusCommutator p.a p.a' ≠ ⊥ := by
  intro h
  apply source.critical_noncommutation geometry p.a p.color_a p.critical
  apply le_bot_iff.mp
  exact p.critical_le_radius_inf_start.trans (h ▸ inf_le_left)

/-- Finiteness comes from the actual far-endpoint Z-layer. -/
theorem radius_finite (p : Counterexample geometry) :
    Finite (radiusCommutator p.a p.a') := by
  let := finite_stabilizer R p.a'
  exact Finite.of_injective
    (inclusion (p.radius_le_end.trans (Z_le_stabilizer R p.a')))
    (inclusion_injective _)

/-- The binary order-two critical commutator is an earlier module consequence,
independent of the unproved radius escape and of the image-order assertion. -/
theorem critical_card (p : Counterexample geometry) (source : LocalSource L R)
    (hb : 2 < geometry.b R) (modules : ModuleFacts source geometry) :
    Nat.card (criticalCommutator p.a p.a') = 2 := by
  let s : BinaryNaturalStructure source :=
    ⟨modules.X_eq_Z, modules.natural, modules.decomposition, modules.disjoint⟩
  rw [criticalCommutator, s.critical_commutator_eq geometry p.a p.color_a p.a' p.critical]
  let : Finite (U R p.a) := Nat.finite_of_card_ne_zero (by
    rw [modules.natural.card_at p.a p.color_a]; decide)
  let : Finite (U R p.a') := Nat.finite_of_card_ne_zero (by
    rw [modules.natural.card_at p.a' p.end_color]; decide)
  let := geometry.U_elementary (by omega) p.a p.color_a
  let := geometry.U_elementary (by omega) p.a' p.end_color
  obtain ⟨hn, hn'⟩ := source.critical_U_mutually_normalize geometry p.a p.color_a p.a' p.critical
  exact card_commutator_eq_two_of_elementary_eight _ _
    (modules.natural.card_at p.a p.color_a) (modules.natural.card_at p.a' p.end_color)
    hn hn' (s.critical_U_noncommutation geometry p.a p.color_a p.a' p.critical)

end Counterexample
end CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape
