module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.PairingControl.FirstPairing.Orientation.ImageCases.Estimates
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.PairingControl.FirstPairing.StepThree.Edges
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.PairingControl.FaithfulSection
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.Initial.Natural.Generation
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Setup.Factorization.Forward
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.EdgeTransfer.Basic


/-!
# Selecting a nonzero moving row in the first image split

Forward nonnormality for the reversed critical pair puts the endpoint in
nu(c). The initial edge identity and the contrary bound at c then show that
R₀ = [V_a,Z_a'] is not contained in D_c.

For any moving neighbor d at a, its local conjugate span contains Z_a and
Vcirc_a. Its commutator with Z_a' contains the order-two critical commutator
and, by faithfulness of the initial natural section, is not contained in Z_a.
It therefore fills the order-four R₀. Since all these conjugates remain moving,
one of them has a commutator escaping D_c. The endpoint inclusion Z_a' ≤ V_c
supplies the row needed by the order-two representation argument.

This selection uses only the earlier initial facts and the contrary bound;
it needs neither the image order nor the first-pairing representation bounds.
All normalization is relative to vertex stabilizers. The fixed-neighbor
normality calculation adapts the independent argument in
Initial/Consequences/DistanceFour.lean; the moving-neighbor existence argument
adapts Orientation/QuotientApplication/Selection.lean.
Source: Meierfrankenfeld--Stellmacher (1993), (4.3.2)(2), printed p.883,
with (2.2)(iv) and (4.3.1)(i)--(iv),(vii).
-/

public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
open scoped commutatorElement
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.PairingControl.FirstPairing.Orientation.ImageCases
variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}
  {geometry : MS93.Geometry R}

private theorem fixed_neighbor_normal (source : LocalSource L R)
    (hb : 2 < geometry.b R) {a d : Vertex R} (ha : color R a = false)
    (had : (cosetGraph R).dist a d = 2)
    (hfixed : Z R d ≤ B R a (geometry.Z_normal a)) :
    ((Z R d ⊔ Z R a).subgroupOf (stabilizer R a)).Normal := by
  have hV : V R a ≤ stabilizer R a :=
    (geometry.V_le_Q hb a ha).trans (fun _ hx => hx.1)
  have hc : ⁅Z R d, Ltilde R a⁆ ≤ Z R a := by
    rw [commutator_comm]
    apply commutator_le.mpr
    intro l hl z hz
    exact ((mem_B_iff R a _ hV z).mp (hfixed hz)).2 l hl
  have hL : Ltilde R a ≤ normalizer (Z R d ⊔ Z R a : Subgroup (FreeAmalgam R)) := by
    apply le_normalizer_iff_commutator_le_right.mpr
    rw [commutator_comm]
    apply (commutator_mono (show Z R d ⊔ Z R a ≤
      commutatorPreimage (stabilizer R a) (Ltilde R a) (Z R a) from ?_) le_rfl).trans
    · exact (commutator_commutatorPreimage_le _ _ _ (Z_normalized R a)).trans le_sup_right
    · exact sup_le (le_commutatorPreimage (hfixed.trans ((EdgeTransfer.B_le_radius hb a ha).trans hV)) hc)
        (le_commutatorPreimage (Z_le_stabilizer R a)
          (le_normalizer_iff_commutator_le_left.mp
            ((Ltilde_le_stabilizer a).trans (Z_normalized R a))))
  have hQ : Q R a ≤ normalizer (Z R d ⊔ Z R a : Subgroup (FreeAmalgam R)) :=
    (le_inf ((Q_le_stabilizer_of_dist_two R a d ha had).trans (Z_normalized R d))
      ((show Q R a ≤ stabilizer R a from fun _ hx => hx.1).trans (Z_normalized R a))).trans
        (normalizer_inf_normalizer_le_normalizer_sup _ _)
  apply normal_subgroupOf_of_le_normalizer
  rw [← source.local_generation a ha]
  exact sup_le hL hQ

/-- The reverse critical path makes the endpoint a moving neighbor of c. -/
theorem endpoint_moving_at_predecessor (source : LocalSource L R)
    (hb : 2 < geometry.b R) (modules : ModuleFacts source geometry)
    (p : Counterexample geometry) : p.a' ∈ movingNeighbors geometry p.c := by
  refine ⟨p.before.1, ?_⟩
  have hr := source.critical_reverse geometry p.a p.color_a p.a' p.end_color p.critical
  have hn := critical_nonnormal_forward R geometry
    (source.adjacent_centralizer geometry.radical_ne_bot) p.a' p.end_color
    (by
      rw [geometry.distance_constant p.a' p.end_color]
      change 0 < geometry.b R
      omega)
    p.a hr p.c (by rw [SimpleGraph.dist_comm]; exact p.before.1) (by
      rw [SimpleGraph.dist_comm (u := p.c), SimpleGraph.dist_comm (u := p.a')]
      exact p.before.2)
  rw [modules.X_eq_Z p.c p.before_color] at hn
  intro hfixed
  exact hn.2 (fixed_neighbor_normal source hb p.before_color p.before.1 hfixed)

/-- Source R₀ escapes D_c by the initial edge equality and step (1) at c. -/
theorem radius_not_le_predecessor_fixed (source : LocalSource L R)
    (hb : 2 < geometry.b R) (modules : ModuleFacts source geometry)
    (transfer : NormalizationTransfer R)
    (initial : ∀ q : Counterexample geometry, Nonempty (InitialFacts q))
    (p : Counterexample geometry)
    (bad : ¬ ⁅V R p.a, Q R p.a⁆ ≤ fixedCore R p.a) :
    ¬ radiusCommutator p.a p.a' ≤ fixedCore R p.c := by
  obtain ⟨ip⟩ := initial p
  obtain ⟨t, ht⟩ := p.exists_before (show 1 ≤ geometry.b R by omega)
  have hct := p.before.adjacent (geometry := geometry) ht
  have hm := endpoint_moving_at_predecessor source hb modules p
  have he := StepThree.moving_commutator_eq_edge_at p (by omega) initial bad
    p.c t p.a' p.before_color hct ht.endpoint_adjacent hm
  rw [ip.radius_eq_edge t ht, ← he]
  obtain ⟨q, hqa, hbad⟩ := contrary_at p bad p.c p.before_color
  obtain ⟨iq⟩ := initial q
  have hmq : p.a' ∈ movingNeighbors geometry q.a := hqa.symm ▸ hm
  simpa only [hqa] using moving_commutator_not_le_fixed hb transfer iq hbad hmq

private theorem moving_neighbor_exists (hb : 2 < geometry.b R)
    (p : Counterexample geometry) (ip : InitialFacts p) :
    ∃ d, d ∈ movingNeighbors geometry p.a := by
  have hV : V R p.a ≤ stabilizer R p.a :=
    (geometry.V_le_Q hb p.a p.color_a).trans (fun _ hx => hx.1)
  have hnot : ¬ V R p.a ≤ B R p.a (geometry.Z_normal p.a) := by
    intro h
    have hcirc : Vcirc R p.a ≤ Z R p.a := by
      rw [Vcirc, commutator_comm]
      apply commutator_le.mpr
      intro l hl v hv
      exact ((mem_B_iff R p.a (geometry.Z_normal p.a) hV v).mp (h hv)).2 l hl
    have hbot : H R p.a = ⊥ := le_bot_iff.mp (by
      rw [← Z_centralizes_Q R p.a p.color_a]
      exact commutator_mono hcirc le_rfl)
    have hc := ip.H_card
    rw [hbot, card_bot] at hc
    omega
  by_contra! h
  apply hnot
  apply iSup_le
  intro d
  apply iSup_le
  intro hd
  have hdist : (cosetGraph R).dist p.a d ≤ 2 := by rwa [SimpleGraph.dist_comm]
  by_cases h0 : (cosetGraph R).dist p.a d = 0
  · have heq := (cosetGraph_connected R).dist_eq_zero_iff.mp h0
    subst d
    exact EdgeTransfer.Z_le_B hb p.a p.color_a
  by_cases h1 : (cosetGraph R).dist p.a d = 1
  · have hadj : Adjacent R p.a d := (cosetGraph_adj R _ _).mp
      (SimpleGraph.dist_eq_one_iff_adj.mp h1)
    exact (EdgeTransfer.edge_Z_le p.a d p.color_a hadj).trans
      (EdgeTransfer.Z_le_B hb p.a p.color_a)
  · have h2 : (cosetGraph R).dist p.a d = 2 := by omega
    exact of_not_not (fun hn => h d ⟨h2, hn⟩)

/-- The conjugates of any moving layer recover the whole endpoint commutator. -/
theorem moving_closure_commutator_eq_radius (source : LocalSource L R)
    (p : Counterexample geometry) (ip : InitialFacts p)
    {d : Vertex R} (hd : d ∈ movingNeighbors geometry p.a) :
    ⁅NormalizerTransfer.conjugatesIn (Z R d) (stabilizer R p.a), Z R p.a'⁆ =
      radiusCommutator p.a p.a' := by
  let K := NormalizerTransfer.conjugatesIn (Z R d) (stabilizer R p.a)
  let C := ⁅K, Z R p.a'⁆
  have hKV : K ≤ V R p.a := by
    apply iSup_le
    intro g
    exact (map_mono (moving_Z_le_V hd)).trans
      (mem_normalizer_iff_map_conj_eq.mp
        (V_normalized p.a ((stabilizer R p.a).inv_mem g.property))).le
  have hCR : C ≤ radiusCommutator p.a p.a' := commutator_mono hKV le_rfl
  have hZK : Z R p.a ≤ K :=
    Initial.Natural.Z_le_conjugatesIn_of_dist_two p.a d p.color_a hd.1
  have hRC : criticalCommutator p.a p.a' ≤ C := commutator_mono hZK le_rfl
  have hnot : ¬ C ≤ Z R p.a := by
    intro h
    have hactor := actor_le_Q source p.color_a ip.natural_section (Z R p.a')
      p.end_Z_le_start_stabilizer ((commutator_mono (ip.moving_generation d hd) le_rfl).trans h)
    exact (source.critical_reverse geometry p.a p.color_a p.a' p.end_color p.critical).2 hactor
  let := p.radius_finite
  let : Finite C := Finite.of_injective (inclusion hCR) (inclusion_injective _)
  have hdiv := card_dvd_of_le hCR
  rw [ip.radius_card] at hdiv
  have htwo : 2 ≤ Nat.card C := by
    rw [← ip.critical_card]
    exact Nat.card_le_card_of_injective (inclusion hRC) (inclusion_injective _)
  have hne : Nat.card C ≠ 2 := by
    intro hc
    have he : criticalCommutator p.a p.a' = C :=
      eq_of_le_of_card_ge hRC (by rw [hc, ip.critical_card])
    exact hnot (he.symm.le.trans (p.critical_le_radius_inf_start.trans inf_le_right))
  have hfour : Nat.card C = 4 := by
    have hposs := Nat.mem_divisors.mpr ⟨hdiv, (by decide : 4 ≠ 0)⟩
    rw [show Nat.divisors 4 = ({1, 2, 4} : Finset ℕ) by decide] at hposs
    simp only [Finset.mem_insert, Finset.mem_singleton] at hposs
    omega
  exact eq_of_le_of_card_ge hCR (by rw [hfour, ip.radius_card])

/-- The stronger endpoint noncontainment selected at the end of printed p.883. -/
theorem exists_moving_endpoint_commutator_not_le_fixed (source : LocalSource L R)
    (hb : 2 < geometry.b R) (modules : ModuleFacts source geometry)
    (transfer : NormalizationTransfer R)
    (initial : ∀ q : Counterexample geometry, Nonempty (InitialFacts q))
    (p : Counterexample geometry)
    (bad : ¬ ⁅V R p.a, Q R p.a⁆ ≤ fixedCore R p.a) :
    ∃ d, d ∈ movingNeighbors geometry p.a ∧
      ¬ ⁅Z R d, Z R p.a'⁆ ≤ fixedCore R p.c := by
  obtain ⟨ip⟩ := initial p
  obtain ⟨d, hd⟩ := moving_neighbor_exists hb p ip
  by_contra! h
  apply radius_not_le_predecessor_fixed source hb modules transfer initial p bad
  rw [← moving_closure_commutator_eq_radius source p ip hd]
  have hnorm : V R p.a ≤ normalizer (fixedCore R p.c : Set (FreeAmalgam R)) :=
    (p.trapped.trans (show Q R p.c ≤ stabilizer R p.c from fun _ hx => hx.1)).trans
      (fixedCore_normalized p.c)
  apply (commutator_mono (show NormalizerTransfer.conjugatesIn (Z R d) (stabilizer R p.a) ≤
    commutatorPreimage (V R p.a) (Z R p.a') (fixedCore R p.c) from ?_) le_rfl).trans
  · exact commutator_commutatorPreimage_le _ _ _ hnorm
  · apply iSup_le
    intro g
    have hg : act R (g : FreeAmalgam R) p.a = p.a := g.property
    have hm := (movingNeighbors_act_iff hb (g : FreeAmalgam R) p.a d p.color_a).mpr hd
    rw [hg] at hm
    change (Z R d).map (MulAut.conj (g : FreeAmalgam R)⁻¹).toMonoidHom ≤ _
    rw [← Z_act]
    exact le_commutatorPreimage (moving_Z_le_V hm) (h _ hm)

/-- The moving-neighbor witness consumed by the small-image representation estimate. -/
theorem exists_moving_commutator_not_le_predecessor_fixed (source : LocalSource L R)
    (hb : 2 < geometry.b R) (modules : ModuleFacts source geometry)
    (transfer : NormalizationTransfer R)
    (initial : ∀ q : Counterexample geometry, Nonempty (InitialFacts q))
    (p : Counterexample geometry)
    (bad : ¬ ⁅V R p.a, Q R p.a⁆ ≤ fixedCore R p.a) :
    ∃ d, d ∈ movingNeighbors geometry p.a ∧
      ¬ ⁅Z R d, V R p.c⁆ ≤ fixedCore R p.c := by
  obtain ⟨d, hd, hne⟩ :=
    exists_moving_endpoint_commutator_not_le_fixed source hb modules transfer initial p bad
  exact ⟨d, hd, fun h => hne ((commutator_mono le_rfl (end_Z_le_predecessor_V p)).trans h)⟩

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.PairingControl.FirstPairing.Orientation.ImageCases
