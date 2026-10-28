module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.PathCentrality.Source44.FixedLines.Reverse
/-!
# The exact selected displacement and its terminal normalizer

For the same simultaneous first selection, the displacement has order four
and is the join of the moved fixed line and the new critical commutator.
The latter line is centralized by the terminal Z-layer. Thus that terminal
layer normalizes the displacement joined with the original Z-layer.

This records an actual source consequence and distinguishes two joins:
the selected product Z_d Z_c is not normalized, whereas [Z_d,Q_c] Z_c
is normalized. The latter cannot be used as a fresh terminal normalizer
failure in a repetition of the initial order-four calculation.

Source: Meierfrankenfeld--Stellmacher (1993), (4.4.1), printed p.892,
penultimate paragraph, using the literal first simultaneous selection.
-/
public section
open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality.Source44
open LocalCommutator LocalCommutator.CriticalCase
variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}
  {source : LocalSource L R} {geometry : Geometry R}

theorem selected_displacement_eq_line_sup_critical (common : CommonFacts R source geometry)
    (hb : 4 < geometry.b R) {a c : Vertex R} (ha : color R a = false)
    (hd : (cosetGraph R).dist a c = 2) (w : BackwardWitness R geometry a c)
    (n : TerminalNeighbor w) {t : Vertex R}
    (hdt : Adjacent R w.backward t) (hct : Adjacent R c t)
    {g : FreeAmalgam R} (hg : g ∈ stabilizer R c)
    (hmove : ¬ Z R n.vertex ≤ normalizer
      (edgeFixedNatural (R := R) (act R g w.backward) (act R g t)))
    (hprod : ¬ Z R n.vertex ≤ normalizer
      (Z R (act R g w.backward) ⊔ Z R c : Subgroup (FreeAmalgam R))) :
    ⁅Z R (act R g w.backward),Q R c⁆ =
      edgeFixedNatural (R := R) (act R g w.backward) (act R g t) ⊔
        ⁅Z R (act R g w.backward),Z R w.predecessor⁆ := by
  let d := act R g w.backward
  let F := edgeFixedNatural (R := R) d (act R g t)
  let D := ⁅Z R d,Z R w.predecessor⁆
  let E := ⁅Z R d,Q R c⁆
  obtain ⟨v,hv,hback,hg',hpred,_⟩ := switched_backward_witness common hb ha hd w n hdt hct hg hmove hprod
  have hcol : color R d = false := (action_preserves_color R g w.backward).trans (w.backward_color ha)
  have hgc : act R g c = c := hg
  have hdist : (cosetGraph R).dist d c = 2 := by
    simpa only [hgc] using (dist_act R g w.backward c).trans (w.backward_distance hd)
  obtain ⟨p⟩ := terminal_new_critical_pair common hb ha hd w n hdist hprod
  have hEcard : Nat.card E = 4 := by
    have hh := EscapeSelection.backward_displacement_card_four common hb ha hd v
    simpa only [hback] using hh
  have hFcard : Nat.card F = 2 := fixed_line_card common hb ha hd w n hcol
    ((adjacent_act_iff R g w.backward t).mpr hdt)
  have hDcard : Nat.card D = 2 := critical_commutator_card common p
  have hDZ : D ≤ Z R w.predecessor := le_normalizer_iff_commutator_le_right.mp
    (((p.reverse common).endpoint_Z_le_start_stabilizer (by omega)).trans (Z_normalized R _))
  have hAQ : Z R n.vertex ≤ Q R w.predecessor := by
    apply Z_le_Q_of_dist_lt R _ (geometry.exists_critical _ n.color)
    rw [geometry.distance_constant _ n.color,SimpleGraph.dist_comm,n.distance]
    change 2 < geometry.b R
    omega
  have hAD : Z R n.vertex ≤ centralizer (D : Set (FreeAmalgam R)) :=
    hAQ.trans ((le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp
      (geometry.centralizes w.predecessor w.predecessor_color))).trans (centralizer_le hDZ))
  have hDE : D ≤ E := commutator_mono le_rfl (w.predecessor_Z_le_center_kernel (by omega))
  have hFE : F ≤ E := fixed_line_le_displacement common hcol hdist
    ((adjacent_act_iff R g w.backward t).mpr hdt)
    (by simpa only [hgc] using (adjacent_act_iff R g c t).mpr hct) hFcard (by
      intro he; change Nat.card (⁅Z R d,Q R c⁆ : Subgroup (FreeAmalgam R)) = 4 at hEcard
      rw [he,card_bot] at hEcard; omega)
  let : Finite E := Nat.finite_of_card_ne_zero (by rw [hEcard]; decide)
  let : Finite D := Nat.finite_of_card_ne_zero (by rw [hDcard]; decide)
  have hnot : ¬ F ≤ D := by
    intro hh
    have he : F = D := eq_of_le_of_card_ge hh (by rw [hFcard,hDcard])
    apply hmove
    change Z R n.vertex ≤ normalizer F
    rw [he]
    exact hAD.trans (Subgroup.centralizer_le_normalizer _)
  have hle : F ⊔ D ≤ E := sup_le hFE hDE
  let : Finite (F ⊔ D : Subgroup (FreeAmalgam R)) :=
    Finite.of_injective (inclusion hle) (inclusion_injective _)
  have hlarge : 2 < Nat.card (F ⊔ D : Subgroup (FreeAmalgam R)) := by
    by_contra! hh
    have he : D = F ⊔ D := eq_of_le_of_card_ge le_sup_right (by omega)
    exact hnot (he ▸ le_sup_left)
  have hdiv : 2 ∣ Nat.card (F ⊔ D : Subgroup (FreeAmalgam R)) :=
    hDcard ▸ card_dvd_of_le le_sup_right
  exact (eq_of_le_of_card_ge hle (by rw [hEcard]; omega)).symm

theorem selected_displacement_sup_normalized (common : CommonFacts R source geometry)
    (hb : 4 < geometry.b R) {a c : Vertex R} (ha : color R a = false)
    (hd : (cosetGraph R).dist a c = 2) (w : BackwardWitness R geometry a c)
    (n : TerminalNeighbor w) {t : Vertex R}
    (hdt : Adjacent R w.backward t) (hct : Adjacent R c t)
    {g : FreeAmalgam R} (hg : g ∈ stabilizer R c)
    (hmove : ¬ Z R n.vertex ≤ normalizer
      (edgeFixedNatural (R := R) (act R g w.backward) (act R g t)))
    (hprod : ¬ Z R n.vertex ≤ normalizer
      (Z R (act R g w.backward) ⊔ Z R c : Subgroup (FreeAmalgam R))) :
    Z R n.vertex ≤ normalizer
      (⁅Z R (act R g w.backward),Q R c⁆ ⊔ Z R c : Subgroup (FreeAmalgam R)) := by
  have hgc : act R g c = c := hg
  have hcol : color R (act R g w.backward) = false :=
    (action_preserves_color R g w.backward).trans (w.backward_color ha)
  have hdist : (cosetGraph R).dist (act R g w.backward) c = 2 := by
    simpa only [hgc] using (dist_act R g w.backward c).trans (w.backward_distance hd)
  obtain ⟨p⟩ := terminal_new_critical_pair common hb ha hd w n hdist hprod
  have hFZ : edgeFixedNatural (R := R) (act R g w.backward) (act R g t) ≤ Z R c :=
    fixed_line_le_common_Z (geometry := geometry) (by omega) hcol w.path.start_color
      ((adjacent_act_iff R g w.backward t).mpr hdt)
      (by simpa only [hgc] using (adjacent_act_iff R g c t).mpr hct)
  have hDZ : ⁅Z R (act R g w.backward),Z R w.predecessor⁆ ≤ Z R w.predecessor :=
    le_normalizer_iff_commutator_le_right.mp
      (((p.reverse common).endpoint_Z_le_start_stabilizer (by omega)).trans (Z_normalized R _))
  have hAQ : Z R n.vertex ≤ Q R w.predecessor := by
    apply Z_le_Q_of_dist_lt R _ (geometry.exists_critical _ n.color)
    rw [geometry.distance_constant _ n.color,SimpleGraph.dist_comm,n.distance]
    change 2 < geometry.b R
    omega
  have hAD := (hAQ.trans ((le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp
      (geometry.centralizes w.predecessor w.predecessor_color))).trans (centralizer_le hDZ))).trans
      (Subgroup.centralizer_le_normalizer _)
  have hAC := ((n.criticalPath common hb ha hd).endpoint_Z_le_start_stabilizer (by omega)).trans
    (Z_normalized R c)
  rw [selected_displacement_eq_line_sup_critical common hb ha hd w n hdt hct hg hmove hprod,
    sup_comm _ (⁅Z R (act R g w.backward),Z R w.predecessor⁆),sup_assoc,
    sup_eq_right.mpr hFZ]
  exact (le_inf hAD hAC).trans (normalizer_inf_normalizer_le_normalizer_sup _ _)

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality.Source44
