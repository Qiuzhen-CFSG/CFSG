module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.Propagation.RadiusFour.Kernel.Actors

/-!
# The normal-radius contradiction in MS93 (4.3.8)

Assumed containment in the fourth predecessor's kernel puts the radius-four
ball in Q_mu, using its established commutation with Z_mu. The reverse
radius noncontainment constructs a new genuine contrary critical pair with
second predecessor mu. Its initial facts supply the lower commutator order
four. The edge calculation gives |H_mu| = 4 and the matching upper bound,
so the larger ball's displacement lies in V_alpha.

The actor at mu escapes Q_alpha. Normal generation in the actual SL3(2)
quotient extends its displacement bound to the local two-residual. Thus the
radius-three span at the first path edge is normal in G_alpha. Source
characteristic faithfulness, as proved in Ball, excludes that normality.
All groups remain literal radius spans inside the free amalgam, with
normality taken only in the indicated finite stabilizer.

Source: Meierfrankenfeld--Stellmacher (1993), printed p.889, penultimate
paragraph of (4.3.8), before the final contradiction for (4.3).
-/

public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.Propagation.RadiusFour.Kernel
variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M} {geometry : Geometry R}

/-- Containment in the fourth kernel, together with the already proved
intersection commutation, places the ball in the actual first-conjugate kernel. -/
theorem ball_le_first_kernel (source : LocalSource L R) (hb : 2 < geometry.b R)
    (forward : ForwardFacts geometry) (p : Counterexample geometry)
    {d t₃ t₅ : Vertex R} (hd : Before p.a p.a' d 4)
    (h₃ : Before p.a p.a' t₃ 3) (h₅ : Before p.a p.a' t₅ 5)
    (w : CentralOrbitWitnesses p d t₃ t₅) (hA : VBall R p.a 4 ≤ Q R d) :
    VBall R p.a 4 ≤ Q R w.mu := by
  have hdc : color R d = false := (hd.color (by decide)).trans p.end_color
  have hμc : color R w.mu = false := by
    rw [← w.first_image, action_preserves_color, p.end_color]
  have hdist : (cosetGraph R).dist d w.mu ≤ 2 := by
    have h₁ := SimpleGraph.dist_eq_one_iff_adj.mpr ((cosetGraph_adj R _ _).mpr
      (hd.adjacent (geometry := geometry) h₃))
    have h₂ := SimpleGraph.dist_eq_one_iff_adj.mpr ((cosetGraph_adj R _ _).mpr
      (adjacent_symm R w.first_adjacent))
    have ht := (cosetGraph_connected R).dist_triangle (u := d) (v := t₃) (w := w.mu)
    omega
  rw [← source.C_eq_Q geometry.radical_ne_bot w.mu hμc]
  refine le_inf (hA.trans (Q_le_stabilizer_of_dist_le_two d w.mu hdc hμc hdist)) ?_
  apply commutator_eq_bot_iff_le_centralizer.mp
  simpa only [inf_eq_left.mpr hA] using inf_commutation source hb forward p hd h₃ h₅ w

/-- A trapped radius group and a radius group escaping in the reverse
direction yield an actual contrary critical configuration. -/
theorem exists_counterexample_of_radius_not_le (source : LocalSource L R)
    {a v : Vertex R} (ha : color R a = false) (hv : color R v = false)
    (hd : (cosetGraph R).dist a v + 2 ≤ geometry.b R)
    (htrap : V R a ≤ Q R v) (hnot : ¬ V R v ≤ Q R a) :
    ∃ q : Counterexample geometry, q.a = a ∧ q.c = v := by
  classical
  have hn : ¬ VBall R v 2 ≤ Q R a := hnot
  obtain ⟨x, hx, hxv, hxQ⟩ : ∃ x, color R x = false ∧
      (cosetGraph R).dist x v ≤ 2 ∧ ¬ Z R x ≤ Q R a := by
    simpa only [Forward.VBall_le_iff hv, not_forall, exists_prop] using hn
  have hmin := criticalDistance_le R x (geometry.exists_critical x hx) hxQ
  rw [geometry.distance_constant x hx] at hmin
  change geometry.b R ≤ (cosetGraph R).dist x a at hmin
  have htri := (cosetGraph_connected R).dist_triangle (u := x) (v := v) (w := a)
  rw [SimpleGraph.dist_comm (u := v) (v := a)] at htri
  have hxa : (cosetGraph R).dist x a = geometry.b R := by omega
  have hxv' : (cosetGraph R).dist x v = 2 := by omega
  have hcrit : CriticalPair R x a (geometry.exists_critical x hx) :=
    ⟨by rw [geometry.distance_constant x hx]; exact hxa, hxQ⟩
  exact ⟨{
    a := a
    a' := x
    c := v
    color_a := ha
    critical := source.critical_reverse geometry x hx a ha hcrit
    before := ⟨by rw [SimpleGraph.dist_comm, hxv'], by
      rw [SimpleGraph.dist_comm (u := a) (v := x), hxa]; omega⟩
    trapped := htrap
  }, rfl, rfl⟩

/-- The earlier edge order and moving-neighbor uniqueness give the exact
order of H at every M-vertex, after a genuine transport of the contrary pair. -/
theorem H_card_four (hb : 0 < geometry.b R)
    (initial : ∀ q : Counterexample geometry, Nonempty (InitialFacts q))
    (control : ∀ q : Counterexample geometry, LocalControl q)
    (rigidity : RigidityFacts geometry) (p : Counterexample geometry)
    (a t : Vertex R) (ha : color R a = false) (hat : Adjacent R a t) :
    Nat.card (H R a) = 4 := by
  obtain ⟨q, hqa, hqt⟩ := counterexample_at_edge p hb a t ha hat
  obtain ⟨v, hvt, hvm, _⟩ := rigidity.moving_Z_unique q t hqt
  have heq := ((control q).H_eq_edge t hqt v hvt hvm).2
  rw [hqa] at heq
  rw [heq]
  exact edge_card p hb initial v t (Rigidity.neighbor_color ha hat hvt) hvt

omit [Finite M] in
/-- Both the actor and the first predecessor moving subgroup lie in the
literal radius-four ball centered at the fourth predecessor. -/
theorem first_moving_le_ball (p : Counterexample geometry)
    {d t₃ t₅ : Vertex R} (hd : Before p.a p.a' d 4)
    (h₃ : Before p.a p.a' t₃ 3) (w : CentralOrbitWitnesses p d t₃ t₅) :
    Vcirc R w.mu ≤ VBall R d 4 := by
  have h₁ := SimpleGraph.dist_eq_one_iff_adj.mpr ((cosetGraph_adj R _ _).mpr w.first_adjacent)
  have h₂ := SimpleGraph.dist_eq_one_iff_adj.mpr ((cosetGraph_adj R _ _).mpr
    (adjacent_symm R (hd.adjacent (geometry := geometry) h₃)))
  have ht := (cosetGraph_connected R).dist_triangle (u := w.mu) (v := t₃) (w := d)
  exact (PairingControl.Geometry.Vcirc_le_V _).trans
    (VBall_le_of_dist_add_le d w.mu 2 4 (by omega))

/-- The order-four lower bound is applied at a newly constructed critical
configuration with second predecessor mu, not transported by an informal WLOG. -/
theorem first_commutator_card_ge_four (source : LocalSource L R) (hb : 2 < geometry.b R)
    (initial : ∀ q : Counterexample geometry, Nonempty (InitialFacts q))
    (control : ∀ q : Counterexample geometry, LocalControl q)
    (backward : BackwardFacts geometry) (forward : ForwardFacts geometry)
    (p : Counterexample geometry) {d t₃ t₅ : Vertex R}
    (hd : Before p.a p.a' d 4) (h₃ : Before p.a p.a' t₃ 3)
    (h₅ : Before p.a p.a' t₅ 5) (w : CentralOrbitWitnesses p d t₃ t₅)
    (hA : VBall R p.a 4 ≤ Q R d) :
    4 ≤ Nat.card (⁅V R p.a, Vcirc R w.mu⁆ : Subgroup (FreeAmalgam R)) := by
  have hμc : color R w.mu = false := by
    rw [← w.first_image, action_preserves_color, p.end_color]
  have hnear : (cosetGraph R).dist p.a w.mu + 2 ≤ geometry.b R := by
    have hpath := h₃.2
    rw [p.distance_eq_b] at hpath
    have h₁ := SimpleGraph.dist_eq_one_iff_adj.mpr ((cosetGraph_adj R _ _).mpr
      (adjacent_symm R w.first_adjacent))
    have ht := (cosetGraph_connected R).dist_triangle (u := p.a) (v := t₃) (w := w.mu)
    omega
  obtain ⟨q, hqa, hqc⟩ := exists_counterexample_of_radius_not_le source p.color_a hμc hnear
    ((VBall_mono R p.a (by decide : 2 ≤ 4)).trans
      (ball_le_first_kernel source hb forward p hd h₃ h₅ w hA))
    (first_radius_not_le source hb initial control backward p w)
  obtain ⟨hi⟩ := initial q
  simpa only [hqa, hqc] using hi.radius_moving_card

/-- The upper and lower commutator orders agree. Consequently the larger
ball has no more displacement than its radius-two subgroup. -/
theorem ball_commutator_le_radius (source : LocalSource L R) (hb : 2 < geometry.b R)
    (initial : ∀ q : Counterexample geometry, Nonempty (InitialFacts q))
    (control : ∀ q : Counterexample geometry, LocalControl q)
    (rigidity : RigidityFacts geometry) (backward : BackwardFacts geometry)
    (forward : ForwardFacts geometry) (p : Counterexample geometry)
    {d t₃ t₅ t : Vertex R} (hd : Before p.a p.a' d 4)
    (h₃ : Before p.a p.a' t₃ 3) (h₅ : Before p.a p.a' t₅ 5)
    (ht : Before p.a' p.a t 1) (w : CentralOrbitWitnesses p d t₃ t₅)
    (hA : VBall R p.a 4 ≤ Q R d) : ⁅VBall R p.a 4, Vcirc R w.mu⁆ ≤ V R p.a := by
  have hμc : color R w.mu = false := by
    rw [← w.first_image, action_preserves_color, p.end_color]
  have hH := H_card_four (by omega : 0 < geometry.b R) initial control rigidity p
    w.mu t₃ hμc w.first_adjacent
  let : Finite (H R w.mu) := Nat.finite_of_card_ne_zero (by rw [hH]; decide)
  have hupper : ⁅VBall R p.a 4, Vcirc R w.mu⁆ ≤ H R w.mu := by
    rw [commutator_comm]
    exact commutator_mono le_rfl (ball_le_first_kernel source hb forward p hd h₃ h₅ w hA)
  let : Finite (⁅VBall R p.a 4, Vcirc R w.mu⁆ : Subgroup (FreeAmalgam R)) :=
    Finite.of_injective (inclusion hupper) (inclusion_injective _)
  have hle : ⁅V R p.a, Vcirc R w.mu⁆ ≤ ⁅VBall R p.a 4, Vcirc R w.mu⁆ :=
    commutator_mono (VBall_mono R p.a (by decide : 2 ≤ 4)) le_rfl
  have heq := eq_of_le_of_card_ge hle ((card_le_of_le hupper).trans (by
    rw [hH]
    exact first_commutator_card_ge_four source hb initial control backward forward p hd h₃ h₅ w hA))
  rw [← heq]
  apply le_normalizer_iff_commutator_le_left.mp
  have hlocal : Vcirc R w.mu ≤ stabilizer R p.a :=
    (first_moving_le_ball p hd h₃ w).trans
      (le_sup_left.trans ((forward.radius_join p d hd t ht).le.trans
        (show Q R t ≤ stabilizer R p.a from fun _ hx => hx.2 p.a
          (adjacent_symm R ht.endpoint_adjacent))))
  exact hlocal.trans (V_normalized p.a)

/-- Normal generation in the actual SL3(2) quotient extends a displacement
bound from an actor outside Q_alpha to the local two-residual. -/
theorem ball_residual_le_radius (source : LocalSource L R)
    (hb : 4 < geometry.b R) (p : Counterexample geometry) (initial : InitialFacts p)
    (J : Subgroup (FreeAmalgam R)) (hJG : J ≤ stabilizer R p.a)
    (hJQ : ¬ J ≤ Q R p.a) (hc : ⁅VBall R p.a 4, J⁆ ≤ V R p.a) :
    ⁅VBall R p.a 4, Ltilde R p.a⁆ ≤ Vcirc R p.a := by
  let S := stabilizer R p.a
  let := finite_stabilizer R p.a
  let W := (VBall R p.a 4).subgroupOf S
  let V₀ := (V R p.a).subgroupOf S
  let J₀ := J.subgroupOf S
  let π := initial.natural_section.projection
  have hWQ := VBall_le_Q p.a p.color_a 4 hb
  have hWG : VBall R p.a 4 ≤ S := hWQ.trans (fun _ hx => hx.1)
  have hVG : V R p.a ≤ S := initial.natural_section.local_group
  let : W.Normal := normal_subgroupOf_of_le_normalizer (VBall_normalized p.a 4)
  let : V₀.Normal := normal_subgroupOf_of_le_normalizer (V_normalized p.a)
  have hker : IsPGroup 2 π.ker := by
    rw [initial.natural_section.module_section.projection_kernel]
    exact (Q_isPGroup R source.two_group source.core_le p.a p.color_a).comap_subtype
  have hpW : IsPGroup 2 W :=
    ((Q_isPGroup R source.two_group source.core_le p.a p.color_a).to_le hWQ).comap_subtype
  have hJ : ¬ J₀ ≤ π.ker := by
    intro h
    apply hJQ
    intro z hz
    have hz' := h (show (⟨z, hJG hz⟩ : S) ∈ J₀ from hz)
    rw [initial.natural_section.module_section.projection_kernel] at hz'
    exact hz'
  have hc₀ : ⁅W, J₀⁆ ≤ V₀ := by
    apply map_le_iff_le_comap.mp
    rw [map_commutator, map_subgroupOf_eq_of_le hWG, map_subgroupOf_eq_of_le hJG]
    exact hc
  have h := map_mono (f := S.subtype)
    (PairingControl.Geometry.LocalProducts.residual_commutator_bound π
      initial.natural_section.module_section.projection_surjective hker W V₀ J₀ hpW hJ hc₀)
  dsimp only [W, V₀] at h
  simpa only [map_commutator, map_subgroupOf_eq_of_le hWG,
    map_subgroupOf_eq_of_le hVG, Vcirc, Ltilde, S] using h

/-- Every subgroup between the radius-two and radius-four balls is
normalized by the residual once its displacement lies in the smaller ball.
For the radius-three ball at the first edge, Q_alpha supplies the other generator. -/
theorem radius_three_normal_of_residual (source : LocalSource L R)
    (p : Counterexample geometry) {t : Vertex R} (hat : Adjacent R p.a t)
    (hc : ⁅VBall R p.a 4, Ltilde R p.a⁆ ≤ V R p.a) :
    ((VBall R t 3).subgroupOf (stabilizer R p.a)).Normal := by
  have hdist : (cosetGraph R).dist p.a t = 1 :=
    SimpleGraph.dist_eq_one_iff_adj.mpr ((cosetGraph_adj R _ _).mpr hat)
  have hsmall : V R p.a ≤ VBall R t 3 := VBall_le_of_dist_add_le t p.a 2 3 (by rw [hdist])
  have hlarge : VBall R t 3 ≤ VBall R p.a 4 :=
    VBall_le_of_dist_add_le p.a t 3 4 (by rw [SimpleGraph.dist_comm, hdist])
  apply normal_subgroupOf_of_le_normalizer
  rw [← source.local_generation p.a p.color_a]
  apply sup_le
  · apply le_normalizer_iff_commutator_le_left.mpr
    exact (commutator_mono hlarge le_rfl).trans (hc.trans hsmall)
  · exact (show Q R p.a ≤ stabilizer R t from fun _ hx => hx.2 t hat).trans
      (VBall_normalized t 3)

/-- The normal-radius contradiction of the penultimate paragraph of (4.3.8).
All actor and commutator-order premises are derived before applying characteristic
faithfulness at the first edge. -/
theorem ball_not_le (source : LocalSource L R) (hb : 2 < geometry.b R)
    (modules : ModuleFacts source geometry)
    (initial : ∀ q : Counterexample geometry, Nonempty (InitialFacts q))
    (control : ∀ q : Counterexample geometry, LocalControl q) (edge : EdgeTransfer geometry)
    (rigidity : RigidityFacts geometry) (backward : BackwardFacts geometry)
    (forward : ForwardFacts geometry) (p : Counterexample geometry)
    {d : Vertex R} (hd : Before p.a p.a' d 4) : ¬ VBall R p.a 4 ≤ Q R d := by
  intro hA
  have hlarge := rigidity.six_lt p
  obtain ⟨t₃, h₃⟩ := p.exists_before (show 3 ≤ geometry.b R by omega)
  obtain ⟨t₅, h₅⟩ := p.exists_before (show 5 ≤ geometry.b R by omega)
  obtain ⟨w⟩ := central_orbit_witnesses source hb modules initial control edge backward
    p d t₃ t₅ hd h₃ h₅
  obtain ⟨t, hat, hdist⟩ := exists_adjacent_dist_sub_one R p.a p.a'
    (p.distance_eq_b.symm ▸ (show 0 < geometry.b R by omega))
  have ht : Before p.a' p.a t 1 := by
    constructor
    · rw [SimpleGraph.dist_comm]
      exact SimpleGraph.dist_eq_one_iff_adj.mpr ((cosetGraph_adj R _ _).mpr hat)
    · simpa only [SimpleGraph.dist_comm] using hdist
  have hJG : Vcirc R w.mu ≤ stabilizer R p.a :=
    (first_moving_le_ball p hd h₃ w).trans
      (le_sup_left.trans ((forward.radius_join p d hd t ht).le.trans
        (show Q R t ≤ stabilizer R p.a from fun _ hx => hx.2 p.a (adjacent_symm R hat))))
  have hJQ : ¬ Vcirc R w.mu ≤ Q R p.a := fun h =>
    first_moving_not_le_product source hb initial control backward p w (h.trans le_sup_right)
  obtain ⟨hi⟩ := initial p
  have hres := ball_residual_le_radius source (by omega) p hi (Vcirc R w.mu) hJG hJQ
    (ball_commutator_le_radius source hb initial control rigidity backward forward p hd h₃ h₅ ht w hA)
  exact radius_three_not_normal source modules (by omega) p.a t p.color_a hat
    (radius_three_normal_of_residual source p hat (hres.trans (PairingControl.Geometry.Vcirc_le_V _)))
end CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.Propagation.RadiusFour.Kernel
