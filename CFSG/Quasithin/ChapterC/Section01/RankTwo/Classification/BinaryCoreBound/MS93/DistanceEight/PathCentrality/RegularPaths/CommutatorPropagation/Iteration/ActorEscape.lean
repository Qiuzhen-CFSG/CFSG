module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.PathCentrality.LocalCommutator.SourceCritical
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.PathCentrality.RegularPaths.CommutatorPropagation.Iteration.Conclusion

/-!
# The terminal radius contradiction using its actual endpoint actor

The actor in the last step of (4.4.4) is Z_(a+2), while the radius group is
V_(a'). Their centers are b-2 steps apart. If a radius-two orbit moves any
element of this actor modulo D_(a'), that orbit escapes Q_(a+2). The source
critical-prefix version of (4.4.1) therefore applies to every orbit that
contributes to the displacement. An orbit with fixed displacement needs no
critical placement.

This proves the full radius calculation and the original terminal contradiction
without the arbitrary-pair LocalCommutatorControl premise. The only earlier
source input retained is the independent nonnatural-section contradiction on
actual critical prefixes, owned by LocalCommutator.CriticalCase. The original
terminal seed and propagation inputs retain their existing producer obligations.

Source: MS93 (4.4.4), printed p.894, using (4.4.1), pp.890--892, and reversed
critical-pair escape (4.3).
-/

@[expose] public section
open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality.RegularPaths.CommutatorPropagation.Iteration.ActorEscape
open LocalCommutator
variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}
variable {source : LocalSource L R} {geometry : Geometry R}

private theorem not_Z_le_proper_natural_sup_fixed
    (common : CommonFacts R source geometry) {c : Vertex R} (hc : color R c = false)
    {K : Subgroup (FreeAmalgam R)} (hK : K ≤ U R c) (hne : K ≠ U R c) :
    ¬ Z R c ≤ K ⊔ fixedCore R c := by
  intro h
  apply hne
  apply le_antisymm hK
  intro u hu
  have hmem := h (U_le_Z R c hu)
  rw [← SetLike.mem_coe, join_fixedCore_eq_mul R K
    (hK.trans ((U_le_Z R c).trans (Z_le_stabilizer R c)))] at hmem
  obtain ⟨k, hk, d, hd, heq⟩ := hmem
  have hdU : d ∈ U R c := by
    have hh := (U R c).mul_mem ((U R c).inv_mem (hK hk)) hu
    rw [← heq, inv_mul_cancel_left] at hh
    exact hh
  have hd1 : d = 1 := by
    have hd' : d ∈ U R c ⊓ centralizer (Ltilde R c : Set (FreeAmalgam R)) := ⟨hdU, hd.2⟩
    rw [Escape.EdgeTransfer.U_fixed_eq_bot (moduleFacts common) c hc] at hd'
    exact hd'
  change k * d = u at heq
  rw [hd1, mul_one] at heq
  rwa [← heq]

/-- A proper natural bound fixes the full radius displacement for an actor
in the Z-layer b-2 steps away. Every moving orbit supplies its own escape. -/
theorem radius_displacement_le_fixed (common : CommonFacts R source geometry)
    (hb : 4 < geometry.b R)
    (exclude : ∀ {d e : Vertex R} (p : CriticalPath R geometry d e),
      ¬ ⁅Z R d, Q R (p.walk.getVert 2)⁆ ≤ fixedCore R (p.walk.getVert 2) →
      ¬ HasNaturalSection R d (p.walk.getVert 2) → False)
    {c e : Vertex R} (hc : color R c = false) (he : color R e = false)
    (hce : (cosetGraph R).dist c e + 2 = geometry.b R)
    {A K : Subgroup (FreeAmalgam R)} (hA : A ≤ Q R c) (hAZ : A ≤ Z R e)
    (hK : K ≤ U R c) (hne : K ≠ U R c)
    (hbound : ⁅V R c, A⁆ ≤ K) : ⁅V R c, A⁆ ≤ fixedCore R c := by
  have hQn : Q R c ≤ normalizer (fixedCore R c : Set (FreeAmalgam R)) :=
    (show Q R c ≤ stabilizer R c from fun _ hx => hx.1).trans (fixedCore_normalized R c)
  suffices hV : V R c ≤ commutatorPreimage (Q R c) A (fixedCore R c) from
    (commutator_mono hV le_rfl).trans
      (commutator_commutatorPreimage_le _ _ _ hQn)
  apply (V_le_iff R hc _).mpr
  intro d hd hdist
  have hdQ : Z R d ≤ Q R c := by
    apply Z_le_Q_of_dist_lt R d (geometry.exists_critical d hd)
    rw [geometry.distance_constant d hd]
    exact lt_of_le_of_lt hdist common.large_distance
  apply le_commutatorPreimage hdQ
  by_cases hdc : d = c
  · subst d
    exact (commutator_mono le_rfl hA).trans_eq (geometry.centralizes c hc) |>.trans bot_le
  have hdist2 : (cosetGraph R).dist d c = 2 := by
    have hpos := (cosetGraph_connected R).pos_dist_of_ne hdc
    have hnot1 : (cosetGraph R).dist d c ≠ 1 := by
      intro h1
      have hadj := (cosetGraph_adj R _ _).mp (SimpleGraph.dist_eq_one_iff_adj.mp h1)
      exact adjacent_color_ne R hadj (hd.trans hc.symm)
    omega
  apply commutator_le.mpr
  intro z hz x hx
  have hxQ := hA hx
  have hs : ⁅localZSpan R d c, zpowers x⁆ ≤ fixedCore R c := by
    by_contra hn
    have hcontrol := SourceCritical.localControl_of_endpoint_movement
      common hb exclude hd hc hdist2 he hce hxQ (hAZ hx) hn
    have hh := hcontrol.2 x hxQ hn
    apply not_Z_le_proper_natural_sup_fixed common hc hK hne
    apply hh.trans
    apply sup_le_sup_right
    rw [commutator_comm]
    exact (commutator_mono (localZSpan_le_V R hdist2.le) (zpowers_le.mpr hx)).trans hbound
  exact hs (commutator_mem_commutator (Z_le_localZSpan R d c hz) (mem_zpowers x))

/-- The natural and fixed summands have trivial intersection, so the same
proper bound kills the actual displacement. -/
theorem radius_displacement_eq_bot (common : CommonFacts R source geometry)
    (hb : 4 < geometry.b R)
    (exclude : ∀ {d e : Vertex R} (p : CriticalPath R geometry d e),
      ¬ ⁅Z R d, Q R (p.walk.getVert 2)⁆ ≤ fixedCore R (p.walk.getVert 2) →
      ¬ HasNaturalSection R d (p.walk.getVert 2) → False)
    {c e : Vertex R} (hc : color R c = false) (he : color R e = false)
    (hce : (cosetGraph R).dist c e + 2 = geometry.b R)
    {A K : Subgroup (FreeAmalgam R)} (hA : A ≤ Q R c) (hAZ : A ≤ Z R e)
    (hK : K ≤ U R c) (hne : K ≠ U R c)
    (hbound : ⁅V R c, A⁆ ≤ K) : ⁅V R c, A⁆ = ⊥ := by
  apply le_bot_iff.mp
  rw [← Escape.EdgeTransfer.U_fixed_eq_bot (moduleFacts common) c hc]
  exact le_inf (hbound.trans hK)
    ((radius_displacement_le_fixed common hb exclude hc he hce hA hAZ hK hne hbound).trans
      inf_le_right)

/-- The literal terminal actor is Z_(p[2]); its distance supplies exactly
the endpoint condition of the radius calculation. -/
theorem contradiction_of_terminal_displacement (common : CommonFacts R source geometry)
    (hb : 6 < geometry.b R)
    (exclude : ∀ {d e : Vertex R} (q : CriticalPath R geometry d e),
      ¬ ⁅Z R d, Q R (q.walk.getVert 2)⁆ ≤ fixedCore R (q.walk.getVert 2) →
      ¬ HasNaturalSection R d (q.walk.getVert 2) → False)
    {a a' : Vertex R} (p : CriticalPath R geometry a a')
    {K : Subgroup (FreeAmalgam R)} (seed : TerminalPropagationSeed p K)
    (hbound : ⁅Z R (p.walk.getVert 2), V R a'⁆ ≤ K) : False := by
  have hlen := p.length_eq_b
  have hc : color R (p.walk.getVert 2) = false :=
    (p.vertex_color (by omega)).mpr (by decide)
  have hdist : (cosetGraph R).dist (p.walk.getVert 2) a' = p.walk.length - 2 := p.dist_end 2
  have hA : Z R (p.walk.getVert 2) ≤ Q R a' := by
    apply Z_le_Q_of_dist_lt R _ (geometry.exists_critical _ hc)
    rw [geometry.distance_constant _ hc, hdist]
    change p.walk.length - 2 < geometry.b R
    omega
  have hce : (cosetGraph R).dist a' (p.walk.getVert 2) + 2 = geometry.b R := by
    rw [SimpleGraph.dist_comm, hdist]
    omega
  have ht : Adjacent R a' (p.walk.getVert (p.walk.length - 1)) := by
    have hh := p.walk.adj_getVert_succ (i := p.walk.length - 1) (by omega)
    rw [show p.walk.length - 1 + 1 = p.walk.length by omega,
      SimpleGraph.Walk.getVert_length] at hh
    exact adjacent_symm R ((cosetGraph_adj R _ _).mp hh)
  have hKU : K ≤ U R a' := by
    rw [seed.terminal_edge]
    exact Escape.EdgeTransfer.edge_commutator_le_natural common.large_distance
      (moduleFacts common) _ _ p.end_color ht
  have hproper : K ≠ U R a' := by
    intro he
    have hcard := Escape.EdgeTransfer.edge_displacement_card_le_four common.large_distance
      (moduleFacts common) _ _ p.end_color ht
    change Nat.card (edgeCommutator R a' (p.walk.getVert (p.walk.length - 1))) ≤ 4 at hcard
    rw [← seed.terminal_edge, he, common.natural.card_at a' p.end_color] at hcard
    omega
  have hzero : ⁅V R a', Z R (p.walk.getVert 2)⁆ = ⊥ :=
    radius_displacement_eq_bot common (by omega) exclude p.end_color hc hce hA le_rfl
      hKU hproper (by rwa [commutator_comm])
  have hVS : V R a' ≤ stabilizer R (p.walk.getVert 2) := by
    apply (V_le_iff R p.end_color _).mpr
    intro d hd hda
    apply geometry.Z_le_stabilizer_of_dist_le_b d hd
    have htri := (cosetGraph_connected R).dist_triangle (u := d) (v := a')
      (w := p.walk.getVert 2)
    rw [SimpleGraph.dist_comm (u := a'), hdist] at htri
    omega
  have hVQ : V R a' ≤ Q R (p.walk.getVert 2) := by
    apply le_kernel_of_normalizes_incident common hc hVS
    intro t ht
    have hE : edgeCommutator R (p.walk.getVert 2) t ≤ Z R (p.walk.getVert 2) :=
      (Escape.EdgeTransfer.edge_commutator_le_natural common.large_distance
        (moduleFacts common) _ _ hc ht).trans (U_le_Z R _)
    exact ((commutator_eq_bot_iff_le_centralizer.mp hzero).trans (centralizer_le hE)).trans
      (Subgroup.centralizer_le_normalizer _)
  apply common.escape a' p.end_color a (p.reverse common).critical (p.walk.getVert 2)
    (by rw [SimpleGraph.dist_comm, p.dist_start (by omega)]) _ hVQ
  rw [SimpleGraph.dist_comm (u := a'), hdist, SimpleGraph.dist_comm (u := a'), ← p.shortest]
  omega

/-- Connect the unchanged propagation premises to the actor-based terminal
contradiction. Only the independent earlier nonnatural branch remains explicit. -/
theorem contradiction_of_local_steps (common : CommonFacts R source geometry)
    (hb : 6 < geometry.b R)
    (exclude : ∀ {d e : Vertex R} (q : CriticalPath R geometry d e),
      ¬ ⁅Z R d, Q R (q.walk.getVert 2)⁆ ≤ fixedCore R (q.walk.getVert 2) →
      ¬ HasNaturalSection R d (q.walk.getVert 2) → False)
    {a a' : Vertex R} (p : CriticalPath R geometry a a') (hp : HasTurnConjugators R p)
    {K : Subgroup (FreeAmalgam R)} (seed : TerminalPropagationSeed p K)
    (hswitch : BackwardEdgeSwitching p K)
    (hdisplacement : K ≤ U R (p.walk.getVert 2) →
      ⁅Z R (p.walk.getVert 2), V R a'⁆ ≤ K) : False :=
  contradiction_of_terminal_displacement common hb exclude p seed
    (hdisplacement (le_second_natural_of_switching common hb p hp seed hswitch))

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality.RegularPaths.CommutatorPropagation.Iteration.ActorEscape
