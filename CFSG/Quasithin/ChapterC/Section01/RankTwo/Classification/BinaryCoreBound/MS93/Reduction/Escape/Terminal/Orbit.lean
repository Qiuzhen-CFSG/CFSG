module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.Propagation
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.Propagation.RadiusFour.Kernel.Intersection

/-!
# The third local orbit and uniform centrality at six

The fourth predecessor moves at the sixth by radius-four noncontainment.
Neighbor rigidity then excludes movement of lambda and forces its natural
intersection at the sixth predecessor to be central. This contains the
order-four radius commutator. Its centrality preserves it under an actual
third local conjugator, identifying the new displacement and both natural
intersections. Both nonmoving Z-join identities are retained for the next
commutator argument.

Source: Meierfrankenfeld--Stellmacher (1993), final paragraph of printed
p.889 and first displayed identities on p.890. The preceding source stages
remain explicit here and are discharged at the final escape boundary.
-/

public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.Terminal
open Propagation Propagation.RadiusFour
variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M} {geometry : Geometry R}

/-- Retain the literal first two local conjugators in the earlier orbit API. -/
@[expose] def centralWitness {p : Counterexample geometry} {d t₃ t₅ : Vertex R}
    (w : PropagationWitnesses p d t₃ t₅) : CentralOrbitWitnesses p d t₃ t₅ where
  mu := w.mu
  lam := w.lam
  first_conjugator := w.first_conjugator
  second_conjugator := w.second_conjugator
  first_local := w.first_local
  second_local := w.second_local
  first_image := w.first_image
  second_image := w.second_image
  first_adjacent := w.first_adjacent
  second_adjacent := w.second_adjacent
  first_displacement := w.first_displacement
  second_displacement := w.second_displacement
  first_intersection := w.first_intersection
  second_intersection := w.second_intersection

/-- Radius-four noncontainment makes the fourth predecessor move at the sixth. -/
theorem fourth_moving_at_six (source : LocalSource L R) (hb : 2 < geometry.b R)
    (propagation : PropagationFacts geometry) (p : Counterexample geometry)
    {d t₅ s : Vertex R} (hd : Before p.a p.a' d 4)
    (h₅ : Before p.a p.a' t₅ 5) (hs : Before p.a p.a' s 6) :
    d ∈ movingNeighbors geometry s := by
  have hdc : color R d = false := (hd.color (by decide)).trans p.end_color
  have hcomm : ⁅VBall R p.a 4, Z R d⁆ ≠ ⊥ := by
    intro heq
    apply (propagation.radius_four p d hd).1
    rw [← source.C_eq_Q geometry.radical_ne_bot d hdc]
    refine le_inf (Kernel.ball_le_stabilizer (geometry := geometry) p.color_a ?_)
      (commutator_eq_bot_iff_le_centralizer.mp heq)
    exact hd.2.trans p.distance_eq_b |>.le
  exact Kernel.moving_of_ball_noncommutation source hb p h₅ hs
    (adjacent_symm R (h₅.adjacent (geometry := geometry) hd)) hdc hcomm

/-- The second local conjugate is still nonmoving at the fourth predecessor. -/
theorem lam_not_moving_at_four (hb : 2 < geometry.b R) (p : Counterexample geometry)
    {d t₃ t₅ : Vertex R} (hd : Before p.a p.a' d 4)
    (w : PropagationWitnesses p d t₃ t₅) : w.lam ∉ movingNeighbors geometry d := by
  have hdc : color R d = false := (hd.color (by decide)).trans p.end_color
  have hfix : act R w.second_conjugator d = d := w.second_local
  have h := PairingControl.FirstPairing.movingNeighbors_act_iff hb w.second_conjugator
    d w.mu hdc
  rw [hfix, w.second_image] at h
  exact fun hm => w.first_not_moving (h.mp hm)

/-- Equality with the fourth Z-layer contradicts the nonzero central plane. -/
theorem lam_Z_ne_four {source : LocalSource L R} (hb : 2 < geometry.b R) (modules : ModuleFacts source geometry)
    (initial : ∀ q : Counterexample geometry, Nonempty (InitialFacts q))
    (p : Counterexample geometry) {d t₃ t₅ : Vertex R}
    (hd : Before p.a p.a' d 4) (h₅ : Before p.a p.a' t₅ 5)
    (w : PropagationWitnesses p d t₃ t₅) : Z R w.lam ≠ Z R d := by
  intro heq
  have hdc : color R d = false := (hd.color (by decide)).trans p.end_color
  have hU : radiusCommutator p.a p.a' ≤ U R d := by
    rw [w.second_displacement, edgeDisplacement, heq]
    exact EdgeTransfer.edge_commutator_le_natural hb modules d t₅ hdc
      (adjacent_symm R (h₅.adjacent (geometry := geometry) hd))
  have hC : radiusCommutator p.a p.a' ≤ localCenter d :=
    w.second_intersection ▸ inf_le_right
  have hz : radiusCommutator p.a p.a' = ⊥ := le_bot_iff.mp (by
    rw [← Rigidity.U_inf_localCenter_eq_bot modules d hdc]
    exact le_inf hU hC)
  obtain ⟨hi⟩ := initial p
  have hcard := hi.radius_card
  rw [hz, card_bot] at hcard
  omega

/-- The second orbit vertex is nonmoving at the sixth predecessor. -/
theorem lam_not_moving_at_six (source : LocalSource L R) (hb : 2 < geometry.b R)
    (modules : ModuleFacts source geometry)
    (initial : ∀ q : Counterexample geometry, Nonempty (InitialFacts q))
    (propagation : PropagationFacts geometry) (p : Counterexample geometry)
    {d t₃ t₅ s : Vertex R} (hd : Before p.a p.a' d 4)
    (h₅ : Before p.a p.a' t₅ 5) (hs : Before p.a p.a' s 6)
    (w : PropagationWitnesses p d t₃ t₅) : w.lam ∉ movingNeighbors geometry s := by
  intro hm
  have hsc : color R s = false := (hs.color (by decide)).trans p.end_color
  have hs₅ := hs.adjacent (geometry := geometry) h₅
  obtain ⟨q, hqa, hqt⟩ := counterexample_at_edge p (by omega) s t₅ hsc hs₅
  obtain ⟨v, _, _, hv⟩ := propagation.moving_Z_unique q t₅ hqt
  rw [hqa] at hv
  exact lam_Z_ne_four hb modules initial p hd h₅ w
    ((hv _ w.second_adjacent hm).trans
      (hv d (adjacent_symm R (h₅.adjacent (geometry := geometry) hd))
        (fourth_moving_at_six source hb propagation p hd h₅ hs)).symm)

/-- The natural intersection at the sixth predecessor is central. -/
theorem lam_natural_inf_six_central (source : LocalSource L R) (hb : 2 < geometry.b R)
    (propagation : PropagationFacts geometry) (p : Counterexample geometry)
    {d t₃ t₅ s : Vertex R} (hd : Before p.a p.a' d 4)
    (h₅ : Before p.a p.a' t₅ 5) (hs : Before p.a p.a' s 6)
    (w : PropagationWitnesses p d t₃ t₅) :
    U R w.lam ⊓ Z R s ≤ localCenter s := by
  by_contra hn
  have hdc : color R d = false := (hd.color (by decide)).trans p.end_color
  have hsc : color R s = false := (hs.color (by decide)).trans p.end_color
  have hd₅ := adjacent_symm R (h₅.adjacent (geometry := geometry) hd)
  have hs₅ := hs.adjacent (geometry := geometry) h₅
  obtain ⟨q, hqa, hqt⟩ := counterexample_at_edge p (by omega) s t₅ hsc hs₅
  have heq := propagation.equal_Z q t₅ hqt w.lam s w.second_adjacent hs₅ hn
  have hds := fourth_moving_at_six source hb propagation p hd h₅ hs
  have hsym := propagation.moving_symmetric q d
  rw [hqa] at hsym
  have hsd := hsym.mp hds
  apply lam_not_moving_at_four hb p hd w
  refine ⟨neighbor_distance_two hdc hd₅ w.second_adjacent ?_, ?_⟩
  · intro e
    have h := hsd.2
    rw [← heq, ← e] at h
    exact h (EdgeTransfer.Z_le_B hb d hdc)
  · simpa only [heq] using hsd.2

/-- The uniform new centrality statement needed by the final reversed pair. -/
theorem radius_central_at_six (source : LocalSource L R) (hb : 2 < geometry.b R)
    (modules : ModuleFacts source geometry)
    (control : ∀ q : Counterexample geometry, LocalControl q) (edge : EdgeTransfer geometry)
    (propagation : PropagationFacts geometry) (p : Counterexample geometry)
    {s : Vertex R} (hs : Before p.a p.a' s 6) :
    radiusCommutator p.a p.a' ≤ localCenter s := by
  have hlarge := propagation.six_lt p
  obtain ⟨d, hd⟩ := p.exists_before (show 4 ≤ geometry.b R by omega)
  obtain ⟨t₃, h₃⟩ := p.exists_before (show 3 ≤ geometry.b R by omega)
  obtain ⟨t₅, h₅⟩ := p.exists_before (show 5 ≤ geometry.b R by omega)
  obtain ⟨w⟩ := propagation.witnesses p d t₃ t₅ hd h₃ h₅
  have hl : color R w.lam = false := Forward.lam_color p (centralWitness w)
  have hsc : color R s = false := (hs.color (by decide)).trans p.end_color
  apply le_trans _ (lam_natural_inf_six_central source hb propagation p hd h₅ hs w)
  rw [w.second_displacement]
  exact le_inf
    (EdgeTransfer.edge_commutator_le_natural hb modules w.lam t₅ hl w.second_adjacent)
    ((edge_le_Z p hb control edge w.lam t₅ hl w.second_adjacent).trans
      (EdgeTransfer.edge_Z_le s t₅ hsc (hs.adjacent (geometry := geometry) h₅)))

/-- The actual third orbit witness and the two preserved Z-joins. -/
structure ThirdOrbitWitnesses (p : Counterexample geometry) (d t₃ t₅ s t₇ : Vertex R) where
  earlier : PropagationWitnesses p d t₃ t₅
  rho : Vertex R
  conjugator : FreeAmalgam R
  local_mem : conjugator ∈ stabilizer R s
  image : act R conjugator earlier.lam = rho
  adjacent : Adjacent R rho t₇
  lam_not_moving : earlier.lam ∉ movingNeighbors geometry s
  first_join : Z R earlier.lam ⊔ Z R d = Z R earlier.mu ⊔ Z R d
  second_join : Z R rho ⊔ Z R s = Z R earlier.lam ⊔ Z R s
  lam_intersection : radiusCommutator p.a p.a' = U R earlier.lam ⊓ localCenter s
  rho_intersection : radiusCommutator p.a p.a' = U R rho ⊓ localCenter s
  displacement : radiusCommutator p.a p.a' = edgeDisplacement rho t₇

/-- Centrality at six fixes R₀ under the third actual local conjugator. -/
theorem third_orbit_witnesses (source : LocalSource L R) (hb : 2 < geometry.b R)
    (modules : ModuleFacts source geometry)
    (initial : ∀ q : Counterexample geometry, Nonempty (InitialFacts q))
    (control : ∀ q : Counterexample geometry, LocalControl q) (edge : EdgeTransfer geometry)
    (propagation : PropagationFacts geometry) (p : Counterexample geometry)
    {d t₃ t₅ s t₇ : Vertex R} (hd : Before p.a p.a' d 4)
    (h₃ : Before p.a p.a' t₃ 3) (h₅ : Before p.a p.a' t₅ 5)
    (hs : Before p.a p.a' s 6) (h₇ : Before p.a p.a' t₇ 7) :
    Nonempty (ThirdOrbitWitnesses p d t₃ t₅ s t₇) := by
  obtain ⟨w⟩ := propagation.witnesses p d t₃ t₅ hd h₃ h₅
  obtain ⟨hi⟩ := initial p
  have hdc : color R d = false := (hd.color (by decide)).trans p.end_color
  have hsc : color R s = false := (hs.color (by decide)).trans p.end_color
  have hl : color R w.lam = false := Forward.lam_color p (centralWitness w)
  have hs₅ := hs.adjacent (geometry := geometry) h₅
  have hs₇ := adjacent_symm R (h₇.adjacent (geometry := geometry) hs)
  obtain ⟨g, hg, hgt⟩ := stabilizer_transitive_neighbors R s hs₅ hs₇
  have hr₇ : Adjacent R (act R g w.lam) t₇ := by
    rw [← hgt]
    exact (adjacent_act_iff R g _ _).mpr w.second_adjacent
  have hc := radius_central_at_six source hb modules control edge propagation p hs
  have hU : radiusCommutator p.a p.a' ≤ U R w.lam := w.second_intersection ▸ inf_le_left
  have hrU : radiusCommutator p.a p.a' ≤ U R (act R g w.lam) := by
    rw [U_act, ← map_eq_of_le_localCenter _ s hc g hg]
    exact map_mono hU
  have hr : color R (act R g w.lam) = false := (action_preserves_color R g _).trans hl
  have hfirst := Kernel.nonmoving_join_conjugate source hb hdc
    (hd.adjacent (geometry := geometry) h₃) w.first_adjacent w.first_not_moving
    w.second_conjugator w.second_local
  rw [w.second_image] at hfirst
  have hn := lam_not_moving_at_six source hb modules initial propagation p hd h₅ hs w
  have hlam := central_plane_eq_edge source hb modules initial control edge p
    w.lam t₅ s hl w.second_adjacent hs₅ _ hU hc hi.radius_card
  have hrho := central_plane_eq_edge source hb modules initial control edge p
    (act R g w.lam) t₇ s hr hr₇ hs₇ _ hrU hc hi.radius_card
  exact ⟨⟨w, act R g w.lam, g, hg, rfl, hr₇, hn, hfirst,
    Kernel.nonmoving_join_conjugate source hb hsc hs₅ w.second_adjacent hn g hg,
    hlam.2, hrho.2, hrho.1⟩⟩

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.Terminal
