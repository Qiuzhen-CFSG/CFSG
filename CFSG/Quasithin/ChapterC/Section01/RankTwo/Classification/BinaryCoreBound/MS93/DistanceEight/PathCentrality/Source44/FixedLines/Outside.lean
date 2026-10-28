module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.PathCentrality.Source44.Counterexample

/-!
# The first terminal fixed line when the displacement escapes B

For the actual backward pair in MS93 (4.4.1), choose the fixed line and the
whole displacement joined with Z_c simultaneously. The latter is not normal
in G_c when the displacement escapes the fixed preimage B_c. Its selected
failure of normalization implies failure for the selected Z-product, so the
proved terminal plane calculation applies and contradicts that same failure.
Consequently the original fixed line lies in the fixed core D_c.

The literal reversed-selection consumer retains the full LocalControlAt
counterexample and discharges its fixed-line premise on the original orbit.
This closes the first terminal selection in the outside-B branch only; the
inside-B case and the final reversed-selection contradiction are separate.

Source: Meierfrankenfeld--Stellmacher (1993), (4.4.1), printed p.892,
penultimate paragraph, using the strengthened simultaneous choice from
(2.1)(vii), pp.855--856.
-/

public section
open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality.Source44
open LocalCommutator LocalCommutator.CriticalCase
variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}
  {source : LocalSource L R} {geometry : Geometry R}

private theorem normalize_displacement_join {G : Type*} [Group G]
    (A C Q H : Subgroup G) (hAQ : A ≤ Q) (hCQ : C ≤ Q)
    (hC : ⁅C,Q⁆ = ⊥) (hH : H ≤ normalizer (A ⊔ C : Subgroup G))
    (hHQ : H ≤ normalizer Q) (hHC : H ≤ normalizer C) :
    H ≤ normalizer (⁅A,Q⁆ ⊔ C : Subgroup G) := by
  have heq : ⁅A ⊔ C,Q⁆ = ⁅A,Q⁆ := by
    let f : Bool → Subgroup G := fun b => if b then A else C
    have hf : (⨆ b, f b) = A ⊔ C := by simp [iSup_bool_eq, f]
    have h := commutator_iSup_of_le f Q (by intro b; cases b <;> assumption)
    rw [hf] at h
    simpa [iSup_bool_eq, f, hC] using h
  apply (le_inf ?_ hHC).trans (normalizer_inf_normalizer_le_normalizer_sup _ _)
  intro g hg
  rw [mem_normalizer_iff_map_conj_eq, ← heq, map_commutator,
    mem_normalizer_iff_map_conj_eq.mp (hH hg),
    mem_normalizer_iff_map_conj_eq.mp (hHQ hg)]

/-- The source fixed-core conclusion from the actual escaping displacement. -/
theorem fixed_line_le_fixedCore_of_displacement_outside_B
    (common : CommonFacts R source geometry)
    (hb : 4 < geometry.b R) {a c : Vertex R} (ha : color R a = false)
    (hd : (cosetGraph R).dist a c = 2) (w : BackwardWitness R geometry a c)
    (n : TerminalNeighbor w) {t : Vertex R}
    (hdt : Adjacent R w.backward t) (hct : Adjacent R c t)
    (hout : ¬ ⁅Z R w.backward,Q R c⁆ ≤ B R c (geometry.Z_normal c)) :
    edgeFixedNatural (R := R) w.backward t ≤ fixedCore R c := by
  by_contra hnot
  have hcol := w.backward_color ha
  have hdist := w.backward_distance hd
  have hcard := fixed_line_card common hb ha hd w n hcol hdt
  have hZQ : Z R w.backward ≤ Q R c := by
    apply Z_le_Q_of_dist_lt R _ (geometry.exists_critical _ hcol)
    rw [geometry.distance_constant _ hcol,hdist]
    change 2 < geometry.b R
    omega
  have hFQ : edgeFixedNatural (R := R) w.backward t ≤ Q R c :=
    inf_le_left.trans ((U_le_Z R w.backward).trans hZQ)
  have hFnot : ¬ ((edgeFixedNatural (R := R) w.backward t).subgroupOf
      (stabilizer R c)).Normal := fun hn =>
    hnot (line_normal_implies_fixed hFQ hcard hn)
  obtain ⟨hFe,hFn⟩ := fixed_line_edge (by omega : 2 < geometry.b R) hcol hdt
  have ht : color R t = true := by
    have hn := adjacent_color_ne R hct
    have hc := w.path.start_color
    cases h : color R t <;> simp_all
  have hCQ : Z R c ≤ Q R c :=
    (Z_le_VBall R c 2).trans (V_le_Q R w.path.start_color (by omega))
  have hJQ : ⁅Z R w.backward,Q R c⁆ ⊔ Z R c ≤ Q R t := by
    apply (sup_le ?_ hCQ).trans (Q_le_adjacent_h R ht hct)
    exact ((displacement_le_U common hcol hdist).trans (U_le_Z R _)).trans hZQ
  obtain ⟨g,hg,hgF,hgJ⟩ := source_2_1_vii R c n.vertex t w.path.start_color hct
    (edgeFixedNatural (R := R) w.backward t) (⁅Z R w.backward,Q R c⁆ ⊔ Z R c)
    hFe hJQ hFn (displacement_join_edge_normal hcol hdt hct) hFnot
    (displacement_join_not_normal common hb hcol w.path.start_color hdist hout)
    (critical_conjugates_sup_edge common (n.criticalPath common hb ha hd) hct)
  have hgc : act R g c = c := hg
  rw [← fixed_line_act] at hgF
  rw [Subgroup.map_sup,map_commutator,← Z_act,← Q_act,← Z_act,hgc] at hgJ
  have hdist' : (cosetGraph R).dist (act R g w.backward) c = 2 := by
    simpa only [hgc] using (dist_act R g w.backward c).trans hdist
  have hcol' : color R (act R g w.backward) = false :=
    (action_preserves_color R g w.backward).trans hcol
  have hAQ : Z R (act R g w.backward) ≤ Q R c := by
    apply Z_le_Q_of_dist_lt R _ (geometry.exists_critical _ hcol')
    rw [geometry.distance_constant _ hcol',hdist']
    change 2 < geometry.b R
    omega
  have hH : Z R n.vertex ≤ stabilizer R c :=
    (n.criticalPath common hb ha hd).endpoint_Z_le_start_stabilizer (by omega)
  have hseed : ¬ Z R n.vertex ≤ normalizer
      (Z R (act R g w.backward) ⊔ Z R c : Subgroup (FreeAmalgam R)) := by
    intro hn
    exact hgJ (normalize_displacement_join _ _ _ _ hAQ hCQ
      (geometry.centralizes c w.path.start_color) hn
      (hH.trans (Q_normalized R c)) (hH.trans (Z_normalized R c)))
  exact hgJ (selected_displacement_sup_normalized common hb ha hd w n hdt hct hg hgF hseed)

/-- The backward displacement remains in the original local orbit. -/
theorem backward_displacement_outside_B
    (hb : 2 < geometry.b R) {a c : Vertex R}
    (w : BackwardWitness R geometry a c)
    (hout : ¬ ⁅Z R a,Q R c⁆ ≤ B R c (geometry.Z_normal c)) :
    ¬ ⁅Z R w.backward,Q R c⁆ ≤ B R c (geometry.Z_normal c) := by
  intro h
  apply hout
  apply (EscapeSelection.map_le_B_act_iff hb w.path.start_color w.conjugator _).mp
  have hgc : act R w.conjugator c = c := w.local_conjugator
  rwa [map_commutator,← Z_act,← Q_act,w.conjugator_image,hgc]

/-- Actual terminal consumer: the source counterexample outside B enters the
reversed selection with its fixed-core premise discharged on the same orbit. -/
theorem second_selection_of_displacement_outside_B
    (common : CommonFacts R source geometry) (hb : 4 < geometry.b R)
    {a c : Vertex R} (ha : color R a = false)
    (hd : (cosetGraph R).dist a c = 2) (w : BackwardWitness R geometry a c)
    (n : TerminalNeighbor w) (hfail : ¬ LocalControlAt R a c)
    {t : Vertex R} (hdt : Adjacent R w.backward t) (hct : Adjacent R c t)
    (hout : ¬ ⁅Z R a,Q R c⁆ ≤ B R c (geometry.Z_normal c)) :
    ∃ g : FreeAmalgam R, act R g w.backward = c ∧
      (¬ LocalControlAt R c (act R g c)) ∧
      (¬ Z R n.vertex ≤ normalizer (edgeFixedNatural (R := R) c (act R g t))) ∧
      (¬ Z R n.vertex ≤ normalizer
        (Z R (act R g c) ⊔ Z R c : Subgroup (FreeAmalgam R))) ∧
      Nonempty (CriticalPath R geometry (act R g c) w.predecessor) ∧
      edgeFixedNatural (R := R) c (act R g t) ≤ fixedCore R (act R g c) := by
  exact second_selection_retains_source_failure common hb ha hd w n hfail hdt hct
    (fixed_line_le_fixedCore_of_displacement_outside_B common hb ha hd w n hdt hct
      (backward_displacement_outside_B (by omega) w hout))

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality.Source44
