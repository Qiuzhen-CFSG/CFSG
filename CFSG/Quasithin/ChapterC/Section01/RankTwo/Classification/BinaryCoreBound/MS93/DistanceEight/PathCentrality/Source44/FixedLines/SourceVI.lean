module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.PathCentrality.Source44.FixedLines.SelectedDisplacement

/-!
# The source-(2.1)(vi) commutator obstruction at the selected terminal pair

The simultaneous first selection retains failure of normalization of
`Z_d ⊔ Z_c` by the terminal layer `Z_lambda`.  Applying source (2.1)(vi) to
the critical pair `(c,lambda)` and the selected distance-two vertex `d` shows
that the opposite commutator cannot be absorbed by the source triple.  This
is the exact sign needed by the printed index-two branch; it is distinct from
the already proved positive normalization of
`[Z_d,Q_c] ⊔ Z_c`.

Source: Meierfrankenfeld--Stellmacher (1993), (2.1)(vi), pp.855--856, and
(4.4.1), p.892.
-/

public section
open Subgroup Stellmacher.PushingUp.AmalgamGraph
open scoped commutatorElement
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality.Source44
open LocalCommutator LocalCommutator.CriticalCase
variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}
  {source : LocalSource L R} {geometry : Geometry R}

/-- The selected terminal failure forces the opposite source-(2.1)(vi)
commutator noncontainment.  The selected distance-two vertex is retained
literally; no replacement normalizer or fixed-line identification is used. -/
theorem selected_source_vi_commutator_not_le
    (common : CommonFacts R source geometry)
    (hb : 4 < geometry.b R) {a c : Vertex R} (ha : color R a = false)
    (hd : (cosetGraph R).dist a c = 2) (w : BackwardWitness R geometry a c)
    (n : TerminalNeighbor w) {d : Vertex R}
    (hdc : (cosetGraph R).dist d c = 2)
    (hprod : ¬ Z R n.vertex ≤ normalizer
      (Z R d ⊔ Z R c : Subgroup (FreeAmalgam R))) :
    ¬ ⁅Z R d, Z R n.vertex⁆ ≤
      ⁅⁅Z R d, Q R c⁆, Z R n.vertex⁆ ⊔ Z R c := by
  intro hcomm
  have hcol : color R d = false :=
    (color_eq_of_dist_even R d c (by rw [hdc]; decide)).trans w.path.start_color
  have hp : CriticalPath R geometry c n.vertex :=
    n.criticalPath common hb ha hd
  have hcrit : CriticalPair R c n.vertex (geometry.exists_critical c w.path.start_color) :=
    hp.critical
  have hδ : Z R d ≤ Q R c := by
    apply Z_le_Q_of_dist_lt R d (geometry.exists_critical d hcol)
    rw [geometry.distance_constant d hcol, hdc]
    change 2 < geometry.b R
    omega
  have hnormal := source_2_1_vi R source geometry c w.path.start_color
    (by
      rw [show criticalDistance R c (geometry.exists_critical c w.path.start_color) =
        geometry.b R from geometry.distance_constant c w.path.start_color]
      omega)
    hcrit d (by rw [SimpleGraph.dist_comm]; exact hdc) hδ hcomm
  exact hprod hnormal.1

/-- On the same selected pair, the terminal action on the displacement plane
has exactly the original critical line as its image. -/
theorem selected_triple_eq_original_critical
    (common : CommonFacts R source geometry)
    (hb : 4 < geometry.b R) {a c : Vertex R} (ha : color R a = false)
    (hd : (cosetGraph R).dist a c = 2) (w : BackwardWitness R geometry a c)
    (n : TerminalNeighbor w) {t : Vertex R}
    (hdt : Adjacent R w.backward t) (hct : Adjacent R c t)
    {g : FreeAmalgam R} (hg : g ∈ stabilizer R c)
    (hmove : ¬ Z R n.vertex ≤ normalizer
      (edgeFixedNatural (R := R) (act R g w.backward) (act R g t)))
    (hprod : ¬ Z R n.vertex ≤ normalizer
      (Z R (act R g w.backward) ⊔ Z R c : Subgroup (FreeAmalgam R))) :
    ⁅⁅Z R (act R g w.backward),Q R c⁆,Z R n.vertex⁆ =
      ⁅Z R c,Z R n.vertex⁆ := by
  let F := edgeFixedNatural (R := R) (act R g w.backward) (act R g t)
  let D := ⁅Z R (act R g w.backward),Z R w.predecessor⁆
  have hgc : act R g c = c := hg
  have hcol : color R (act R g w.backward) = false :=
    (action_preserves_color R g w.backward).trans (w.backward_color ha)
  have hdist : (cosetGraph R).dist (act R g w.backward) c = 2 := by
    simpa only [hgc] using (dist_act R g w.backward c).trans (w.backward_distance hd)
  obtain ⟨p⟩ := terminal_new_critical_pair common hb ha hd w n hdist hprod
  have hFZ : F ≤ Z R c := fixed_line_le_common_Z (geometry := geometry) (by omega)
    hcol w.path.start_color ((adjacent_act_iff R g w.backward t).mpr hdt)
    (by simpa only [hgc] using (adjacent_act_iff R g c t).mpr hct)
  have hDZ : D ≤ Z R w.predecessor := le_normalizer_iff_commutator_le_right.mp
    (((p.reverse common).endpoint_Z_le_start_stabilizer (by omega)).trans (Z_normalized R _))
  have hAQ : Z R n.vertex ≤ Q R w.predecessor := by
    apply Z_le_Q_of_dist_lt R _ (geometry.exists_critical _ n.color)
    rw [geometry.distance_constant _ n.color,SimpleGraph.dist_comm,n.distance]
    change 2 < geometry.b R
    omega
  have hDA : D ≤ centralizer (Z R n.vertex : Set (FreeAmalgam R)) :=
    hDZ.trans ((commutator_eq_bot_iff_le_centralizer.mp
      (geometry.centralizes w.predecessor w.predecessor_color)).trans (centralizer_le hAQ))
  have hFA : F ≤ normalizer (Z R n.vertex) :=
    hFZ.trans (((n.criticalPath common hb ha hd).reverse common).endpoint_Z_le_start_stabilizer
      (by omega) |>.trans (Z_normalized R _))
  have hcomm := commutator_eq_of_centralizing_sup
    (V := Z R n.vertex) (C := D) (X := F) (B := ⁅Z R (act R g w.backward),Q R c⁆)
    (by rw [selected_displacement_eq_line_sup_critical common hb ha hd w n hdt hct hg hmove hprod];
        exact sup_comm _ _) hDA hFA
  rw [commutator_comm (Z R n.vertex) F,
    commutator_comm (Z R n.vertex) ⁅Z R (act R g w.backward),Q R c⁆] at hcomm
  exact hcomm.symm.trans (critical_moved_line_commutator common
    (n.criticalPath common hb ha hd) hFZ hmove)

/-- The remaining movement is on the selected whole seed, beyond its
controlled displacement plane.  It is nontrivial modulo the original Z_c. -/
theorem selected_commutator_not_le_center_Z
    (common : CommonFacts R source geometry)
    (hb : 4 < geometry.b R) {a c : Vertex R} (ha : color R a = false)
    (hd : (cosetGraph R).dist a c = 2) (w : BackwardWitness R geometry a c)
    (n : TerminalNeighbor w) {t : Vertex R}
    (hdt : Adjacent R w.backward t) (hct : Adjacent R c t)
    {g : FreeAmalgam R} (hg : g ∈ stabilizer R c)
    (hmove : ¬ Z R n.vertex ≤ normalizer
      (edgeFixedNatural (R := R) (act R g w.backward) (act R g t)))
    (hprod : ¬ Z R n.vertex ≤ normalizer
      (Z R (act R g w.backward) ⊔ Z R c : Subgroup (FreeAmalgam R))) :
    ¬ ⁅Z R (act R g w.backward),Z R n.vertex⁆ ≤ Z R c := by
  have hgc : act R g c = c := hg
  have hdist : (cosetGraph R).dist (act R g w.backward) c = 2 := by
    simpa only [hgc] using (dist_act R g w.backward c).trans (w.backward_distance hd)
  have hh := selected_source_vi_commutator_not_le common hb ha hd w n hdist hprod
  rw [selected_triple_eq_original_critical common hb ha hd w n hdt hct hg hmove hprod,
    sup_eq_right.mpr (le_normalizer_iff_commutator_le_left.mp
      ((n.criticalPath common hb ha hd).endpoint_Z_le_start_stabilizer (by omega) |>.trans
        (Z_normalized R _)))] at hh
  exact hh

/-- A literal crossing element carries the residual terminal movement.  The
opposite radius estimate forces this element outside the predecessor kernel. -/
theorem selected_crossing_element
    (common : CommonFacts R source geometry)
    (hb : 4 < geometry.b R) {a c : Vertex R} (ha : color R a = false)
    (hd : (cosetGraph R).dist a c = 2) (w : BackwardWitness R geometry a c)
    (n : TerminalNeighbor w) {t : Vertex R}
    (hdt : Adjacent R w.backward t) (hct : Adjacent R c t)
    {g : FreeAmalgam R} (hg : g ∈ stabilizer R c)
    (hmove : ¬ Z R n.vertex ≤ normalizer
      (edgeFixedNatural (R := R) (act R g w.backward) (act R g t)))
    (hprod : ¬ Z R n.vertex ≤ normalizer
      (Z R (act R g w.backward) ⊔ Z R c : Subgroup (FreeAmalgam R))) :
    ∃ x ∈ Z R (act R g w.backward), x ∉ Q R w.predecessor ∧
      ∃ z ∈ Z R n.vertex, ⁅x,z⁆ ∉ Z R c := by
  classical
  have hn := selected_commutator_not_le_center_Z common hb ha hd w n hdt hct hg hmove hprod
  have hex : ∃ x ∈ Z R (act R g w.backward), ∃ z ∈ Z R n.vertex, ⁅x,z⁆ ∉ Z R c := by
    by_contra! h
    exact hn (commutator_le.mpr h)
  obtain ⟨x,hx,z,hz,hxz⟩ := hex
  refine ⟨x,hx,?_,z,hz,hxz⟩
  intro hxQ
  have hgc : act R g c = c := hg
  have hdist : (cosetGraph R).dist (act R g w.backward) c = 2 := by
    simpa only [hgc] using (dist_act R g w.backward c).trans (w.backward_distance hd)
  have hbound := opposite_intersection_bound common hb ha hd w n hdist.le
  rw [commutator_comm] at hbound
  exact hxz (hbound (commutator_mem_commutator (show x ∈ Z R (act R g w.backward) ⊓ Q R w.predecessor from ⟨hx,hxQ⟩) hz))

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality.Source44
