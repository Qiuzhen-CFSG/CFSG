module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.SylowTerminalSix
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.SylowTrappedExclusion

/-!
# Terminal whole-core comparison on four generating shifts

For the image-sixteen replacement at distance greater than four, a fourth
backward shift transports the preceding core containment to the opposite
side of the same edge. Both whole cores therefore lie in both actual small
movers. If those movers differ, their index-four intersection bounds each
core-product image by four. This argument does not infer mover equality
from quadraticity or from one-sided core containment.

The critical line also belongs to the intermediate whole omega center:
the intermediate core lies in the last mover, which centralizes that line.
The line has order two and remains noncentral in the intermediate stabilizer.
The original-radical application constructs the whole shift chain and the
fourth edge transporter, discharging the orbit and containment premises.
Both moved covers and every central attachment are retained.

The internal import reuses the neighboring-seed radius lemma within this
source proof family. Mover equality, the remaining (5.10)--(5.11) contradiction,
other radical images and the distance-four whole-core estimates remain open.

Source: Meierfrankenfeld--Stellmacher, Pushing up weak BN-pairs of rank two
(1993), (5.10), the first paragraph of printed p.923.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped commutatorElement Pointwise
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive
universe u
variable {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
  {h : SmallMSPair KnownSimple.IsKnownSimple L R} {e : CentralMarking L}
  {hz : center (L ⧸ pCore 2 L) = ⊥} {hn : InitialNatural h e hz}
  {d : Replacement L R}

include e hz hn in
/-- Terminal core containment puts the actual critical line in the whole
intermediate omega center. The line still has order two and is noncentral
in the intermediate stabilizer. -/
theorem orbit_terminal_line_in_omega_knownSimple
    (hb : 4 < replacementDistance h d)
    (hcard : Nat.card (d.radical.map (SourceReduction.projection h e hz hn d)) = 16)
    {a a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a a')
    (q : BackwardShift (h := h) p) (r : BackwardShift (h := h) q.path)
    (t : BackwardShift (h := h) r.path)
    (hr : SylowTerminalPath.OrbitPrefix (h := h) r.path (replacementDistance h d)) :
    let z := r.path.walk.getVert (r.path.walk.length-2)
    let D := ⁅Z d.radical t.start,Z d.radical z⁆
    Nat.card D = 2 ∧ D ≤ X d.radical r.start ∧
      ¬ D ≤ centralizer (stabilizer d.radical r.start : Set (FreeAmalgam d.radical)) := by
  let z := r.path.walk.getVert (r.path.walk.length-2)
  let D := ⁅Z d.radical t.start,Z d.radical z⁆
  have ht := SylowShiftChain.two_backward_shifts_small_moving_knownSimple
    (e := e) (hz := hz) (hn := hn) hb q.path r t
  have hsmall : (Q d.radical z).relIndex (Z d.radical t.start) < 4 := by rw [ht.2.1]; decide
  have hfix := SylowTrappedMover.sixteen_common_kernel_centralizer_knownSimple
    (e := e) (hz := hz) (hn := hn) hb hcard t.path hsmall ht.2.2.2.2
  dsimp only at hfix
  rw [t.first] at hfix
  have hcore := orbit_terminal_core_containment_knownSimple hb hcard p q r t hr
  have hDC : D ≤ centralizer (Q d.radical r.start : Set (FreeAmalgam d.radical)) :=
    le_centralizer_iff.mp ((hcore.trans hfix.1.symm.le).trans inf_le_right)
  have hDZ : D ≤ Z d.radical t.start :=
    ((critical_Z_commutator_le_moving (h := h) t.path).trans inf_le_left).trans
      (DistanceEight.U_le_Z d.radical t.start)
  have hDQ : D ≤ Q d.radical r.start :=
    (hDZ.trans (neighbor_seed_le_radius t.adjacent_start t.adjacent_shift)).trans
      ((replacementGeometry h d).V_le_Q (by omega : 2 < replacementDistance h d) r.start r.path.start_color)
  let := (replacementGeometry h d).Z_elementary (replacementDistance_pos h d) t.start t.path.start_color
  refine ⟨ht.2.2.2.1,?_,ht.1⟩
  intro x hx
  exact mem_omegaCenter_iff.mpr ⟨hDQ hx,elemPow_eq_one_of_isElementaryAbelian x (hDZ hx),hDC hx⟩

include e hz hn in
/-- A fourth actual shift transports the preceding core containment in the
opposite direction along the same edge. Thus both whole cores lie in both
small movers, without assuming that either mover equals the other. -/
theorem four_shift_core_product_knownSimple
    (hb : 4 < replacementDistance h d)
    (hcard : Nat.card (d.radical.map (SourceReduction.projection h e hz hn d)) = 16)
    {a a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a a')
    (q : BackwardShift (h := h) p) (r : BackwardShift (h := h) q.path)
    (t : BackwardShift (h := h) r.path) (v : BackwardShift (h := h) t.path)
    (hr : SylowTerminalPath.OrbitPrefix (h := h) r.path (replacementDistance h d))
    (hv : act d.radical v.transporter (t.path.walk.getVert 1) = v.edge) :
    let J := SmallMover.join (U d.radical t.start) (Q d.radical t.start) (Q d.radical v.edge) 4
    let E := SmallMover.join (U d.radical v.start) (Q d.radical v.start) (Q d.radical v.edge) 4
    Q d.radical t.start ≤ E ∧ Q d.radical v.start ≤ J ∧
      Q d.radical t.start ⊔ Q d.radical v.start ≤ J ⊓ E := by
  have ht : SylowTerminalPath.OrbitPrefix (h := h) t.path (replacementDistance h d) := by
    intro i hi hl
    exact SylowTerminalPath.orbitPrefix_backwardShift hb r.path t hr i (Nat.lt_succ_of_lt hi) hl
  have hforward := orbit_terminal_core_containment_knownSimple hb hcard q.path r t v ht
  have hprevious := orbit_terminal_core_containment_knownSimple hb hcard p q r t hr
  have hsecond : t.path.walk.getVert 2 = r.start := by
    simpa only [Nat.zero_add,SimpleGraph.Walk.getVert_zero] using t.overlap 0 (Nat.zero_le _)
  have hstart : act d.radical v.transporter r.start = v.start := by
    simpa only [hsecond] using v.start_eq
  have hedge : act d.radical v.transporter t.edge = v.edge := by
    simpa only [t.first] using hv
  have hfix : act d.radical v.transporter t.start = t.start := v.transporter_mem
  have hback := map_mono (f := (MulAut.conj v.transporter⁻¹).toMonoidHom) hprevious
  rw [SmallMover.join_map _ (MulAut.conj _).injective,←Q_act,←U_act,←Q_act,←Q_act,
    hstart,hfix,hedge] at hback
  have hj := SylowAdjacent.sixteen_edge_small_mover_knownSimple
    (e := e) (hz := hz) (hn := hn) hb hcard t.path.start_color v.adjacent_start
  have he := SylowAdjacent.sixteen_edge_small_mover_knownSimple
    (e := e) (hz := hz) (hn := hn) hb hcard v.path.start_color v.adjacent_shift
  exact ⟨hforward,hback,le_inf (sup_le hj.1 hback) (sup_le hforward he.1)⟩

include e hz hn in
/-- If the two actual movers are unequal, their index-four intersection
bounds each image of the product of the two whole cores by four. -/
theorem four_shift_unequal_core_indices_knownSimple
    (hb : 4 < replacementDistance h d)
    (hcard : Nat.card (d.radical.map (SourceReduction.projection h e hz hn d)) = 16)
    {a a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a a')
    (q : BackwardShift (h := h) p) (r : BackwardShift (h := h) q.path)
    (t : BackwardShift (h := h) r.path) (v : BackwardShift (h := h) t.path)
    (hr : SylowTerminalPath.OrbitPrefix (h := h) r.path (replacementDistance h d))
    (hv : act d.radical v.transporter (t.path.walk.getVert 1) = v.edge)
    (hne : SmallMover.join (U d.radical v.start) (Q d.radical v.start) (Q d.radical v.edge) 4 ≠
      SmallMover.join (U d.radical t.start) (Q d.radical t.start) (Q d.radical v.edge) 4) :
    (Q d.radical t.start).relIndex (Q d.radical t.start ⊔ Q d.radical v.start) ≤ 4 ∧
      (Q d.radical v.start).relIndex (Q d.radical t.start ⊔ Q d.radical v.start) ≤ 4 := by
  let J := SmallMover.join (U d.radical t.start) (Q d.radical t.start) (Q d.radical v.edge) 4
  let E := SmallMover.join (U d.radical v.start) (Q d.radical v.start) (Q d.radical v.edge) 4
  have hprod := (four_shift_core_product_knownSimple hb hcard p q r t v hr hv).2.2
  have hj := SylowAdjacent.sixteen_edge_small_mover_knownSimple
    (e := e) (hz := hz) (hn := hn) hb hcard t.path.start_color v.adjacent_start
  have he := SylowAdjacent.sixteen_edge_small_mover_knownSimple
    (e := e) (hz := hz) (hn := hn) hb hcard v.path.start_color v.adjacent_shift
  have hint := (SylowAdjacent.sixteen_unequal_neighbor_movers_knownSimple
    (e := e) (hz := hz) (hn := hn) hb hcard t.path.start_color
    v.adjacent_start v.adjacent_shift hne).2.1
  have hQJ : (Q d.radical t.start).relIndex (J ⊓ E) = 4 := by
    have hwhole := relIndex_mul_relIndex (Q d.radical t.start) J (Q d.radical v.edge) hj.1 hj.2.1
    rw [hj.2.2.1,hj.2.2.2.1] at hwhole
    have hh := relIndex_mul_relIndex (Q d.radical t.start) (J ⊓ E) (Q d.radical v.edge)
      (le_sup_left.trans hprod) (inf_le_left.trans hj.2.1)
    rw [hint,←hwhole] at hh
    omega
  have hQE : (Q d.radical v.start).relIndex (J ⊓ E) = 4 := by
    have hwhole := relIndex_mul_relIndex (Q d.radical v.start) E (Q d.radical v.edge) he.1 he.2.1
    rw [he.2.2.1,he.2.2.2.1] at hwhole
    have hh := relIndex_mul_relIndex (Q d.radical v.start) (J ⊓ E) (Q d.radical v.edge)
      (le_sup_right.trans hprod) (inf_le_left.trans hj.2.1)
    rw [hint,←hwhole] at hh
    omega
  let := finite_stabilizer d.radical t.start
  let : Finite (J ⊓ E : Subgroup (FreeAmalgam d.radical)) := Finite.of_injective
    (inclusion ((inf_le_left.trans hj.2.1).trans
      (fun _ hx => hx.2 _ (adjacent_symm d.radical v.adjacent_start)))) (inclusion_injective _)
  exact ⟨(relIndex_le_of_le_right hprod index_ne_zero_of_finite).trans_eq hQJ,
    (relIndex_le_of_le_right hprod index_ne_zero_of_finite).trans_eq hQE⟩

include e hz hn in
/-- The original restricted radical supplies the four shifts, the same
edge transporter, the two whole-core containments and the noncentral omega
line. In the unequal-mover branch both core-product images have order at
most four. No core-containment or path-orbit premise remains in this application. -/
theorem original_radical_terminal_core_product_knownSimple
    (hb : 4 < replacementDistance h d)
    (hcard : Nat.card (d.radical.map (SourceReduction.projection h e hz hn d)) = 16)
    {a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) a')
    (hfirst : p.walk.getVert 1 = beta d.radical) :
    let T := ((R.subgroupOf (L ⊔ R)).subgroupOf d.overgroup).map (embedM d.radical)
    ∃ q₀ : BackwardShift (h := h) p,
      act d.radical q₀.transporter (beta d.radical) = q₀.edge ∧
      T.map (MulAut.conj q₀.transporter⁻¹).toMonoidHom = Q d.radical q₀.edge ∧
      T.map (MulAut.conj q₀.transporter⁻¹).toMonoidHom ⊔ Z d.radical a' =
        stabilizer d.radical (alpha d.radical) ∧
      ∃ c c', ∃ p₀ : CriticalPath d.radical (replacementGeometry h d) c c',
      SylowTerminalPath.ShiftChain (h := h) q₀.path p₀ (replacementDistance h d) ∧
      ∃ (q : BackwardShift (h := h) p₀) (r : BackwardShift (h := h) q.path)
        (t : BackwardShift (h := h) r.path) (v : BackwardShift (h := h) t.path),
      SylowTerminalPath.OrbitPrefix (h := h) r.path (replacementDistance h d) ∧
      act d.radical v.transporter (t.path.walk.getVert 1) = v.edge ∧
      let J := SmallMover.join (U d.radical t.start) (Q d.radical t.start) (Q d.radical v.edge) 4
      let E := SmallMover.join (U d.radical v.start) (Q d.radical v.start) (Q d.radical v.edge) 4
      let D := ⁅Z d.radical v.start,Z d.radical (t.path.walk.getVert (t.path.walk.length-2))⁆
      Q d.radical t.start ≤ E ∧ Q d.radical v.start ≤ J ∧
      Q d.radical t.start ⊔ Q d.radical v.start ≤ J ⊓ E ∧
      Nat.card D = 2 ∧ D ≤ X d.radical t.start ∧
      (¬ D ≤ centralizer (stabilizer d.radical t.start : Set (FreeAmalgam d.radical))) ∧
      (E ≠ J →
        (Q d.radical t.start).relIndex (Q d.radical t.start ⊔ Q d.radical v.start) ≤ 4 ∧
        (Q d.radical v.start).relIndex (Q d.radical t.start ⊔ Q d.radical v.start) ≤ 4) := by
  obtain ⟨q₀,hqe,hqT,hqgen,c,c',p₀,hchain,q,r,t,hr,_⟩ :=
    original_radical_orbit_terminal_normalization_knownSimple hb hcard p hfirst
  obtain ⟨v,hv⟩ := SylowShiftChain.backwardShift_with_edge hb hcard t.path
  have ht : SylowTerminalPath.OrbitPrefix (h := h) t.path (replacementDistance h d) := by
    intro i hi hl
    exact SylowTerminalPath.orbitPrefix_backwardShift hb r.path t hr i (Nat.lt_succ_of_lt hi) hl
  have hc := four_shift_core_product_knownSimple hb hcard p₀ q r t v hr hv
  have hl := orbit_terminal_line_in_omega_knownSimple hb hcard q.path r t v ht
  exact ⟨q₀,hqe,hqT,hqgen,c,c',p₀,hchain,q,r,t,v,hr,hv,hc.1,hc.2.1,hc.2.2,
    hl.1,hl.2.1,hl.2.2,four_shift_unequal_core_indices_knownSimple hb hcard p₀ q r t v hr hv⟩

end AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
