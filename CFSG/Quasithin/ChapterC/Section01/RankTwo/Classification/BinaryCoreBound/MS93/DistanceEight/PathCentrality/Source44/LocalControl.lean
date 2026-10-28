module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.PathCentrality.Source44.FixedLines.Outside

/-!
# The terminal exclusion and natural source spans in MS93 (4.4.1)

The source fixed line, when contained in the neighboring fixed core, equals
its critical commutator. Indeed both are lines in a displacement group of
order four and both centralize the retained endpoint. Distinct lines would
make the whole displacement centralize that endpoint, contradicting the
backward witness's nonzero triple commutator.

Outside B, the first simultaneous choice places the edge fixed line in D.
The reversed choice transports it into the new vertex center. Select a new
backward witness with the retained predecessor as endpoint; the line is
unchanged by that local conjugator and hence is its critical commutator.
The original terminal layer centralizes it by distance at most four,
contradicting its chosen movement. This proves all radius-two displacements
lie in B. The previously proved escaping-neighbor argument now constructs
an actual natural section for every nonfixed source span.

The final consumer proves both local-control clauses on literal critical
prefixes. No critical image order is assumed for the selected replacement.
Source: Meierfrankenfeld--Stellmacher, Pushing up weak BN-pairs of rank two
(1993), (4.4.1), pp.890--892, particularly the final two choices on p.892.
-/
public section
open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality.Source44
open LocalCommutator LocalCommutator.CriticalCase
variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}
  {source : LocalSource L R} {geometry : Geometry R}

theorem fixed_line_eq_critical_of_fixedCore
    (common : CommonFacts R source geometry) (hb : 4 < geometry.b R)
    {a c : Vertex R} (ha : color R a = false)
    (hd : (cosetGraph R).dist a c = 2) (w : BackwardWitness R geometry a c)
    {t : Vertex R} (hdt : Adjacent R w.backward t) (hct : Adjacent R c t)
    (hcard : Nat.card (edgeFixedNatural (R := R) w.backward t) = 2)
    (hcore : edgeFixedNatural (R := R) w.backward t ≤ fixedCore R c) :
    edgeFixedNatural (R := R) w.backward t = ⁅Z R w.backward,Z R w.predecessor⁆ := by
  let F := edgeFixedNatural (R := R) w.backward t
  let D := ⁅Z R w.backward,Z R w.predecessor⁆
  let E := ⁅Z R w.backward,Q R c⁆
  have hEcard : Nat.card E = 4 := EscapeSelection.backward_displacement_card_four common hb ha hd w
  have hDcard : Nat.card D = 2 := critical_commutator_card common (w.shifted ha (by omega))
  have hDE : D ≤ E := commutator_mono le_rfl (w.predecessor_Z_le_center_kernel (by omega))
  have hFE : F ≤ E := fixed_line_le_displacement common (w.backward_color ha)
    (w.backward_distance hd) hdt hct hcard (by
      intro he; dsimp only [E] at hEcard; rw [he,card_bot] at hEcard; omega)
  have hFZ : F ≤ Z R c := fixed_line_le_common_Z (geometry := geometry) (by omega)
    (w.backward_color ha) w.path.start_color hdt hct
  have hFC : F ≤ centralizer (Z R w.endpoint : Set (FreeAmalgam R)) := by
    have h := (le_inf hFZ hcore).trans
      (Escape.Propagation.Rigidity.Z_inf_fixedCore_le_localCenter source c w.path.start_color)
    rw [Escape.Propagation.Rigidity.localCenter_eq] at h
    exact (h.trans inf_le_right).trans
      (centralizer_le (w.path.endpoint_Z_le_start_stabilizer (by omega)))
  have hDV : D ≤ V R w.predecessor :=
    (le_normalizer_iff_commutator_le_right.mp
      (((w.shifted ha (by omega)).reverse common).endpoint_Z_le_start_stabilizer (by omega)
        |>.trans (Z_normalized R _))).trans (Z_le_VBall R _ 2)
  have hDC : D ≤ centralizer (Z R w.endpoint : Set (FreeAmalgam R)) :=
    hDV.trans (commutator_eq_bot_iff_le_centralizer.mp (w.predecessor_V_centralizes_endpoint hb))
  let : Finite E := Nat.finite_of_card_ne_zero (by rw [hEcard]; decide)
  let : Finite D := Nat.finite_of_card_ne_zero (by rw [hDcard]; decide)
  have hFD : F ≤ D := by
    by_contra hn
    have hJE : F ⊔ D ≤ E := sup_le hFE hDE
    let : Finite (F ⊔ D : Subgroup (FreeAmalgam R)) :=
      Finite.of_injective (inclusion hJE) (inclusion_injective _)
    have hlarge : 2 < Nat.card (F ⊔ D : Subgroup (FreeAmalgam R)) := by
      by_contra! hh
      have he : D = F ⊔ D := eq_of_le_of_card_ge le_sup_right (by omega)
      exact hn (he ▸ le_sup_left)
    have hdiv : 2 ∣ Nat.card (F ⊔ D : Subgroup (FreeAmalgam R)) :=
      hDcard ▸ card_dvd_of_le le_sup_right
    have he : F ⊔ D = E := eq_of_le_of_card_ge hJE (by rw [hEcard]; omega)
    apply w.triple_ne
    apply commutator_eq_bot_iff_le_centralizer.mpr
    change E ≤ _
    rw [← he]
    exact sup_le hFC hDC
  exact eq_of_le_of_card_ge hFD (by rw [hDcard]; exact hcard.ge)


theorem false_of_terminal_displacement_outside_B
    (common : CommonFacts R source geometry) (hb : 4 < geometry.b R)
    {a c : Vertex R} (ha : color R a = false)
    (hd : (cosetGraph R).dist a c = 2) (w : BackwardWitness R geometry a c)
    (n : TerminalNeighbor w)
    (hout : ¬ ⁅Z R a,Q R c⁆ ≤ B R c (geometry.Z_normal c)) : False := by
  obtain ⟨t,hdt,hct⟩ := exists_common_neighbor_of_dist_two R w.backward c (w.backward_distance hd)
  have hcore := fixed_line_le_fixedCore_of_displacement_outside_B common hb ha hd w n hdt hct
    (backward_displacement_outside_B (by omega) w hout)
  obtain ⟨g,hgc,hmove,hprod,⟨p⟩,hD⟩ := second_selection_core_transport common hb ha hd w n hdt hct hcore
  let d := act R g c
  let s := act R g t
  let F := edgeFixedNatural (R := R) c s
  have hds : Adjacent R d s := (adjacent_act_iff R g c t).mpr hct
  have hcs : Adjacent R c s := by simpa only [hgc] using (adjacent_act_iff R g w.backward t).mpr hdt
  have hdc : (cosetGraph R).dist d c = 2 := by
    simpa only [d,hgc,SimpleGraph.dist_comm] using (dist_act R g c w.backward).trans
      (by rw [SimpleGraph.dist_comm]; exact w.backward_distance hd)
  have hcd : (cosetGraph R).dist c d = 2 := by rw [SimpleGraph.dist_comm]; exact hdc
  have hcol : color R d = false := (action_preserves_color R g c).trans w.path.start_color
  have hout' : ¬ ⁅Z R c,Q R d⁆ ≤ B R d (geometry.Z_normal d) := by
    intro hin
    apply backward_displacement_outside_B (by omega) w hout
    apply (EscapeSelection.map_le_B_act_iff (by omega) w.path.start_color g _).mp
    rwa [map_commutator,← Z_act,← Q_act,hgc]
  have hFZ : F ≤ Z R d := fixed_line_le_common_Z (geometry := geometry) (by omega)
    w.path.start_color hcol hcs hds
  have hFC : F ≤ centralizer (stabilizer R d : Set (FreeAmalgam R)) := by
    have hh := (le_inf hFZ hD).trans
      (Escape.Propagation.Rigidity.Z_inf_fixedCore_le_localCenter source d hcol)
    rw [Escape.Propagation.Rigidity.localCenter_eq] at hh
    exact hh.trans inf_le_right
  obtain ⟨k,hk,hn,htriple⟩ := exists_unnormalized_displacement common hb w.path.start_color hcd p hout'
  have hkd : act R k d = d := hk
  have hcrit : ¬ Z R (act R k c) ≤ Q R (p.walk.getVert (p.walk.length - 2)) := by
    intro hin
    exact hn (normalizes_displacement_of_containment common hb w.path.start_color hcd p hk hin)
  have hdist : (cosetGraph R).dist (act R k c) d = 2 := by
    simpa only [hkd] using (dist_act R k c d).trans hcd
  obtain ⟨back,hback⟩ := (cosetGraph_connected R).exists_walk_length_eq_dist (act R k c) d
  let v : BackwardWitness R geometry c d := {
    endpoint := w.predecessor
    path := p
    backward := act R k c
    conjugator := k
    local_conjugator := hk
    conjugator_image := rfl
    backwardWalk := back
    backward_length := hback.trans hdist
    noncontainment := hcrit
    triple_ne := htriple }
  have hFn : stabilizer R d ≤ normalizer F :=
    (le_centralizer_iff.mp hFC).trans (Subgroup.centralizer_le_normalizer _)
  have hfixed : edgeFixedNatural (R := R) v.backward (act R k s) = F := by
    change edgeFixedNatural (R := R) (act R k c) (act R k s) = F
    rw [fixed_line_act]
    exact mem_normalizer_iff_map_conj_eq.mp (hFn ((stabilizer R d).inv_mem hk))
  have hvs : Adjacent R v.backward (act R k s) := (adjacent_act_iff R k c s).mpr hcs
  have hds' : Adjacent R d (act R k s) := by simpa only [hkd] using (adjacent_act_iff R k d s).mpr hds
  have hFcard : Nat.card F = 2 := fixed_line_card common hb ha hd w n w.path.start_color hcs
  have heq : F = ⁅Z R v.backward,Z R v.predecessor⁆ := by
    have hh := fixed_line_eq_critical_of_fixedCore common hb w.path.start_color hcd v hvs hds'
      (by rwa [hfixed]) (by rwa [hfixed])
    rwa [hfixed] at hh
  have hFpred : F ≤ Z R v.predecessor := heq ▸
    le_normalizer_iff_commutator_le_right.mp
      (((v.shifted w.path.start_color (by omega)).reverse common).endpoint_Z_le_start_stabilizer (by omega)
        |>.trans (Z_normalized R _))
  have hlamQ : Z R n.vertex ≤ Q R v.predecessor := by
    apply Z_le_Q_of_dist_lt R _ (geometry.exists_critical _ n.color)
    rw [geometry.distance_constant _ n.color,SimpleGraph.dist_comm]
    have ht := (cosetGraph_connected R).dist_triangle
      (u := v.predecessor) (v := w.predecessor) (w := n.vertex)
    have hv : (cosetGraph R).dist v.predecessor w.predecessor = 2 := v.predecessor_distance (by omega)
    rw [hv,n.distance] at ht
    change (cosetGraph R).dist v.predecessor n.vertex < geometry.b R
    omega
  apply hmove
  exact (hlamQ.trans ((le_centralizer_iff.mp
    (commutator_eq_bot_iff_le_centralizer.mp (geometry.centralizes v.predecessor v.predecessor_color))).trans
      (centralizer_le hFpred))).trans (Subgroup.centralizer_le_normalizer _)


theorem displacement_le_B
    (common : CommonFacts R source geometry) (hb : 4 < geometry.b R)
    {a c : Vertex R} (ha : color R a = false) (hc : color R c = false)
    (hd : (cosetGraph R).dist a c = 2) :
    ⁅Z R a,Q R c⁆ ≤ B R c (geometry.Z_normal c) := by
  by_contra hout
  obtain ⟨e,⟨p⟩⟩ := CriticalPath.exists_from (geometry := geometry) hc
  obtain ⟨w⟩ := exists_backwardWitness_of_displacement_outside_B common hb ha hd p hout
  obtain ⟨n⟩ := EscapeSelection.terminalNeighbor_of_escape common hb ha w
    ⟨a,by rw [SimpleGraph.dist_comm]; exact hd,hout⟩
  exact false_of_terminal_displacement_outside_B common hb ha hd w n hout

theorem hasNaturalSection_of_nonfixed
    (common : CommonFacts R source geometry) (hb : 4 < geometry.b R)
    {a c : Vertex R} (ha : color R a = false) (hc : color R c = false)
    (hd : (cosetGraph R).dist a c = 2)
    (hn : ¬ ⁅Z R a,Q R c⁆ ≤ fixedCore R c) : HasNaturalSection R a c := by
  by_contra hnone
  obtain ⟨w⟩ := backward_witness common hb ha hc hd hn hnone
  obtain ⟨r,hr,hout⟩ := escaping_neighbor common hb ha hc hd hn hnone w
  have hrcol : color R r = false :=
    (color_eq_of_dist_even R c r (by rw [hr]; decide)).symm.trans hc
  exact hout (displacement_le_B common hb hrcol hc (by rw [SimpleGraph.dist_comm]; exact hr))

theorem critical_prefix_localControl
    (common : CommonFacts R source geometry) (hb : 4 < geometry.b R)
    {a e : Vertex R} (p : CriticalPath R geometry a e)
    (hn : ¬ ⁅Z R a,Q R (p.walk.getVert 2)⁆ ≤ fixedCore R (p.walk.getVert 2)) :
    LocalControlAt R a (p.walk.getVert 2) := by
  have htwo : 2 ≤ p.walk.length := by rw [p.length_eq_b]; omega
  exact NaturalCase.localControl_of_naturalSection_and_critical_prefix common hb p hn
    (hasNaturalSection_of_nonfixed common hb p.start_color
      ((p.vertex_color htwo).mpr (by decide)) (p.dist_start htwo) hn)

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality.Source44
