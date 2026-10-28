module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.SylowReverseComparison
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.SylowTrappedExclusion

import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.SylowReverseComparison

/-!
# Whole-core containment and the common reverse omega line

For a small critical pair and a small backward shift, normalization of the
full restricted backward kernel joined with the starting seed forces the
whole starting core into the backward small mover. The strict slice bound
makes this kernel escape the Baumann slice. If the core were omitted, the
opposite mover and the critical endpoint would generate the local residual,
forcing a small invariant radius section into that same slice.

The small mover centralizes the entire backward critical line. Core
containment therefore puts the line in the whole starting omega center.
Applying this argument to every literal reverse backward shift in the
image-sixteen branch beyond distance six gives a common order-two line,
centralized by every corresponding reverse small mover. The original
radical, its transporter, both moved covers and all central attachments are
retained in the final application.

This supplies the reverse whole-core and omega estimates in MS93 (5.10).
Residual generation by the two reverse movers, centrality in the full local
stabilizer, mover equality and the terminal distance contradiction remain
further source obligations. The internal imports reuse the neighboring-seed
radius inclusion and the original-radical shift selection in this family.

Source: Meierfrankenfeld--Stellmacher, Pushing up weak BN-pairs of rank two
(1993), (5.5)(c), (5.9)--(5.10), printed pp.915--923, especially p.923.
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
/-- A normalized full backward kernel forces whole-core containment in its
small mover. The backward critical line consequently lies in the whole
intermediate omega center, while the kernel still escapes the Baumann slice. -/
theorem backward_normalized_kernel_core_containment_knownSimple
    (hb : 4 < replacementDistance h d)
    (hcard : Nat.card (d.radical.map (SourceReduction.projection h e hz hn d)) = 16)
    {a z : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a z)
    (hsmall : (Q d.radical z).relIndex (Z d.radical a) < 4)
    (q : BackwardShift (h := h) p)
    (hqsmall : (Q d.radical (p.walk.getVert (p.walk.length-2))).relIndex
      (Z d.radical q.start) < 4)
    (hnorm : Z d.radical z ≤ normalizer
      (((Z d.radical q.start ⊓ Q d.radical (p.walk.getVert (p.walk.length-2))) ⊔
        Z d.radical a : Subgroup (FreeAmalgam d.radical)) : Set (FreeAmalgam d.radical))) :
    let K := Z d.radical q.start ⊓ Q d.radical (p.walk.getVert (p.walk.length-2))
    let E := SmallMover.join (U d.radical q.start) (Q d.radical q.start) (Q d.radical q.edge) 4
    let H := ⁅Z d.radical q.start,Z d.radical (p.walk.getVert (p.walk.length-2))⁆
    (¬ K ≤ B d.radical a ((replacementGeometry h d).Z_normal _)) ∧
      Q d.radical a ≤ E ∧ E ≤ centralizer (H : Set (FreeAmalgam d.radical)) ∧
      Nat.card H = 2 ∧ H ≤ X d.radical a := by
  have hb2 : 2 < replacementDistance h d := by omega
  let s := fullSymmetricAction_knownSimple h e hz hn d hb2
  have hc := DistanceTwo.centralLayer_knownSimple G L R h e hz hn d
  let c := p.walk.getVert (p.walk.length-2)
  let K := Z d.radical q.start ⊓ Q d.radical c
  let N := K ⊔ Z d.radical a
  let E := SmallMover.join (U d.radical q.start) (Q d.radical q.start) (Q d.radical q.edge) 4
  let H := ⁅Z d.radical q.start,Z d.radical c⁆
  have hki : K.relIndex (Z d.radical q.start) = 2 := by
    rw [show K = Z d.radical q.start ⊓ Q d.radical c from rfl,inf_relIndex_left]
    exact (small_critical_indices s hc q.path hqsmall).1
  have hstrict : 2 < (B d.radical a ((replacementGeometry h d).Z_normal _)).relIndex
      (U d.radical q.start) := by
    have hh := SylowForwardSpan.sixteen_small_forward_slice_strict_at_knownSimple
      (e := e) (hz := hz) (hn := hn) hb hcard p hsmall
    have hm : (B d.radical a ((replacementGeometry h d).Z_normal _)).map
        (MulAut.conj q.transporter⁻¹).toMonoidHom = B d.radical a ((replacementGeometry h d).Z_normal _) :=
      mem_normalizer_iff_map_conj_eq.mp (Escape.Propagation.Rigidity.B_normalized
        (geometry := replacementGeometry h d) hb2 a p.start_color
        ((stabilizer d.radical a).inv_mem q.transporter_mem))
    rw [←q.start_eq,U_act,←hm,relIndex_map_map_of_injective _ _ (MulAut.conj _).injective]
    exact hh
  let := finite_Z d.radical q.start
  have hnot : ¬ K ≤ B d.radical a ((replacementGeometry h d).Z_normal _) := by
    intro hKB
    have hi : (B d.radical a ((replacementGeometry h d).Z_normal _)).relIndex
        (Z d.radical q.start) ≤ 2 :=
      (relIndex_le_of_le_left hKB index_ne_zero_of_finite).trans_eq hki
    have hj := relIndex_le_of_le_right (H := B d.radical a ((replacementGeometry h d).Z_normal _))
      (DistanceEight.U_le_Z d.radical q.start) index_ne_zero_of_finite
    exact (Nat.not_le_of_gt hstrict) (hj.trans hi)
  have hfix := SylowSmallMovers.small_critical_kernel_small_movers_knownSimple
    (e := e) (hz := hz) (hn := hn) hb q.path hqsmall
  have hT := SylowLarge.sixteen_edge_relative_normalizer_knownSimple
    (e := e) (hz := hz) (hn := hn) hb2 hcard q.path.start_color q.adjacent_shift
  dsimp only at hfix
  rw [q.first,hT] at hfix
  have hEK : E ≤ normalizer (K : Set (FreeAmalgam d.radical)) := hfix.2.2.1
  have hEH : E ≤ centralizer (H : Set (FreeAmalgam d.radical)) := hfix.2.1
  have hET : E ≤ Q d.radical q.edge := SmallMover.join_le _ _ _ _
  have hTa : Q d.radical q.edge ≤ stabilizer d.radical a :=
    fun _ hx => hx.2 _ (adjacent_symm d.radical q.adjacent_start)
  have hEN : E ≤ normalizer (N : Set (FreeAmalgam d.radical)) :=
    (le_inf hEK ((hET.trans hTa).trans (Z_normalized d.radical a))).trans
      (normalizer_inf_normalizer_le_normalizer_sup _ _)
  have hZV : Z d.radical q.start ≤ V d.radical a :=
    neighbor_seed_le_radius q.adjacent_start q.adjacent_shift
  have hNV : N ≤ V d.radical a := sup_le (inf_le_left.trans hZV) (Z_le_VBall d.radical a 2)
  have hVG : V d.radical a ≤ stabilizer d.radical a :=
    (replacementGeometry h d).V_local a p.start_color (by
      rw [(replacementGeometry h d).distance_constant a p.start_color]
      exact hb2)
  let := finite_stabilizer d.radical a
  let : Finite (Z d.radical q.start ⊔ Z d.radical a : Subgroup (FreeAmalgam d.radical)) :=
    Finite.of_injective (inclusion (sup_le (hZV.trans hVG) (Z_le_stabilizer d.radical a)))
      (inclusion_injective _)
  have hNi : (Z d.radical a).relIndex N ≤ 8 :=
    (relIndex_le_of_le_right (show N ≤ Z d.radical q.start ⊔ Z d.radical a from
      sup_le_sup inf_le_left le_rfl) index_ne_zero_of_finite).trans
        (SylowSpanSelection.adjacent_seed_span_index_le_eight
          (e := e) (hz := hz) (hn := hn) hb p.start_color q.adjacent_start q.adjacent_shift)
  have hres : ¬ Ltilde d.radical a ≤ normalizer (N : Set (FreeAmalgam d.radical)) := by
    intro hnN
    exact hnot (le_sup_left.trans (residual_small_radius_le_slice_knownSimple (e := e)
      hb2 p.start_color N hNV hnN hNi))
  have hcore : Q d.radical a ≤ E := by
    by_contra hnQ
    have hg := sixteen_opposite_residual_of_core_not_le_knownSimple
      (e := e) (hz := hz) (hn := hn) hb hcard p.start_color
      q.adjacent_start q.adjacent_shift (Z d.radical z) q.generation hnQ
    exact hres (hg.2.trans (sup_le hEN hnorm))
  have hHZ : H ≤ Z d.radical q.start :=
    ((critical_Z_commutator_le_moving (h := h) q.path).trans inf_le_left).trans
      (DistanceEight.U_le_Z d.radical q.start)
  have hHQ : H ≤ Q d.radical a := (hHZ.trans hZV).trans
    ((replacementGeometry h d).V_le_Q hb2 a p.start_color)
  have hHC : H ≤ centralizer (Q d.radical a : Set (FreeAmalgam d.radical)) :=
    le_centralizer_iff.mp (hcore.trans hEH)
  let := (replacementGeometry h d).Z_elementary (replacementDistance_pos h d) q.start q.path.start_color
  refine ⟨hnot,hcore,hEH,small_critical_commutator_card s hc q.path hqsmall,?_⟩
  intro x hx
  exact mem_omegaCenter_iff.mpr ⟨hHQ hx,elemPow_eq_one_of_isElementaryAbelian x (hHZ hx),hHC hx⟩

include e hz hn in
set_option maxHeartbeats 300000 in
/-- Every reverse backward seed on the actual five-shift configuration gives
the same order-two line in the intermediate whole omega center. Each reverse
small mover contains the intermediate whole core and centralizes that line. -/
theorem five_shift_reverse_omega_knownSimple
    (hb : 6 < replacementDistance h d)
    (hcard : Nat.card (d.radical.map (SourceReduction.projection h e hz hn d)) = 16)
    {a a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a a')
    (q : BackwardShift (h := h) p) (r : BackwardShift (h := h) q.path)
    (t : BackwardShift (h := h) r.path) (v : BackwardShift (h := h) t.path)
    (w : BackwardShift (h := h) v.path)
    (hr : SylowTerminalPath.OrbitPrefix (h := h) r.path (replacementDistance h d))
    (hv : act d.radical v.transporter (t.path.walk.getVert 1) = v.edge)
    (hne : SmallMover.join (U d.radical v.start) (Q d.radical v.start) (Q d.radical v.edge) 4 ≠
      SmallMover.join (U d.radical t.start) (Q d.radical t.start) (Q d.radical v.edge) 4) :
    let z := v.path.walk.getVert (v.path.walk.length-2)
    ∃ p' : CriticalPath d.radical (replacementGeometry h d) z w.start,
      (∀ i, p'.walk.getVert i = w.path.walk.getVert (w.path.walk.length-i)) ∧
      ∃ b : BackwardShift (h := h) p',
        act d.radical b.transporter (p'.walk.getVert 1) = b.edge ∧
        let H := ⁅Z d.radical b.start,Z d.radical v.start⁆
        Nat.card H = 2 ∧ H ≤ X d.radical z ∧
        ∀ b' : BackwardShift (h := h) p',
          let E := SmallMover.join (U d.radical b'.start) (Q d.radical b'.start) (Q d.radical b'.edge) 4
          Q d.radical z ≤ E ∧ E ≤ centralizer (H : Set (FreeAmalgam d.radical)) ∧
          ⁅Z d.radical b'.start,Z d.radical v.start⁆ = H ∧
          ¬ Z d.radical b'.start ⊓ Q d.radical v.start ≤
            B d.radical z ((replacementGeometry h d).Z_normal _) := by
  have hb4 : 4 < replacementDistance h d := by omega
  let s := fullSymmetricAction_knownSimple h e hz hn d (by omega)
  have hc := DistanceTwo.centralLayer_knownSimple G L R h e hz hn d
  let z := v.path.walk.getVert (v.path.walk.length-2)
  let p' : CriticalPath d.radical (replacementGeometry h d) z w.start :=
    ⟨w.path.end_color,w.path.walk.reverse,
      by rw [SimpleGraph.Walk.length_reverse,w.path.shortest,SimpleGraph.dist_comm],
      critical_reverse_pair s hc w.path⟩
  have hrev : ∀ i, p'.walk.getVert i = w.path.walk.getVert (w.path.walk.length-i) :=
    fun i => SimpleGraph.Walk.getVert_reverse _ i
  have hchoice := SylowShiftChain.backwardShift_with_edge
    (h := h) (e := e) (hz := hz) (hn := hn) hb4 hcard p'
  let b := Classical.choose hchoice
  have hbact := Classical.choose_spec hchoice
  have hlocs := reverse_backward_seed_locations (h := h) (d := d)
    (a := t.start) (a' := r.path.walk.getVert (r.path.walk.length-2)) hb t.path v w p' hrev b
  let cp := Classical.choose hlocs
  have hQ := (Classical.choose_spec hlocs).2.1
  have hC := (Classical.choose_spec hlocs).2.2
  have hpair (b' : BackwardShift (h := h) p') :
      (Q d.radical v.start).relIndex
        (Q d.radical v.start ⊔ (Z d.radical b.start ⊔ Z d.radical b'.start)) = 2 ∧
      Nat.card (⁅Z d.radical b.start,Z d.radical v.start⁆ : Subgroup (FreeAmalgam d.radical)) = 2 ∧
      ⁅Z d.radical b.start,Z d.radical v.start⁆ = ⁅Z d.radical b'.start,Z d.radical v.start⁆ := by
    have hlocs' := reverse_backward_seed_locations (h := h) (d := d)
      (a := t.start) (a' := r.path.walk.getVert (r.path.walk.length-2)) hb t.path v w p' hrev b'
    let cp' := Classical.choose hlocs'
    have hQ' := (Classical.choose_spec hlocs').2.1
    have hC' := (Classical.choose_spec hlocs').2.2
    exact four_shift_terminal_seed_pair_knownSimple (h := h) (e := e) (hz := hz) (hn := hn)
      hb4 hcard p q r t v hr hv hne cp cp' hQ hQ' hC hC'
  have hHcard := (hpair b).2.1
  have hpre : p'.walk.getVert (p'.walk.length-2) = v.start := by
    rw [hrev]
    have hl : w.path.walk.length = replacementDistance h d := w.path.length_eq_b
    have hl' : p'.walk.length = replacementDistance h d := p'.length_eq_b
    rw [show w.path.walk.length-(p'.walk.length-2)=2 by omega]
    simpa only [Nat.zero_add,SimpleGraph.Walk.getVert_zero] using w.overlap 0 (Nat.zero_le _)
  have hs₀ := SylowShiftChain.two_backward_shifts_small_moving_knownSimple
    (e := e) (hz := hz) (hn := hn) hb4 t.path v w
  have hs : (Q d.radical z).relIndex (Z d.radical w.start) < 4 := by rw [hs₀.2.1]; decide
  have hs' : (Q d.radical w.start).relIndex (Z d.radical z) < 4 := by
    rw [(small_critical_indices s hc w.path hs).2]; decide
  have hgen := four_shift_unequal_omega_not_centrally_generated_knownSimple
    (h := h) (e := e) (hz := hz) (hn := hn) hb4 hcard p q r t v hr hv hne w.start w.path.start_color
  have hZX : Z d.radical w.start ≤ X d.radical w.start := by
    apply (replacementGeometry h d).omega_bound w.start w.path.start_color
    rw [(replacementGeometry h d).distance_constant w.start w.path.start_color]
    exact replacementDistance_pos h d
  have hall (b' : BackwardShift (h := h) p') :
      let E := SmallMover.join (U d.radical b'.start) (Q d.radical b'.start) (Q d.radical b'.edge) 4
      let H := ⁅Z d.radical b'.start,Z d.radical v.start⁆
      (¬ Z d.radical b'.start ⊓ Q d.radical v.start ≤
        B d.radical z ((replacementGeometry h d).Z_normal _)) ∧
        Q d.radical z ≤ E ∧ E ≤ centralizer (H : Set (FreeAmalgam d.radical)) ∧
        Nat.card H = 2 ∧ H ≤ X d.radical z := by
    have hi := (hpair b').1
    have hsmall : (Q d.radical v.start).relIndex (Z d.radical b'.start) < 4 := by
      have hzidx : (Q d.radical v.start).relIndex
          (Q d.radical v.start ⊔ (Z d.radical b.start ⊔ Z d.radical b'.start)) ≠ 0 := by
        rw [hi]; decide
      have hle := relIndex_le_of_le_right
        (H := Q d.radical v.start)
        (show Z d.radical b'.start ≤ Q d.radical v.start ⊔
          (Z d.radical b.start ⊔ Z d.radical b'.start) from le_sup_right.trans le_sup_right) hzidx
      omega
    have hn' := backward_full_omega_normalization_of_not_centrally_generated s hc (by omega) p' hs' b' hgen
    have hs'' : (Q d.radical (p'.walk.getVert (p'.walk.length-2))).relIndex
        (Z d.radical b'.start) < 4 := by rwa [hpre]
    have hh := backward_normalized_kernel_core_containment_knownSimple
      (e := e) (hz := hz) (hn := hn) hb4 hcard p' hs' b' hs'' (hZX.trans hn')
    dsimp only at hh ⊢
    rwa [hpre] at hh
  refine ⟨p',hrev,b,hbact,hHcard,(hall b).2.2.2.2,?_⟩
  intro b'
  have hh := hall b'
  have he := (hpair b').2.2.symm
  exact ⟨hh.2.1,hh.2.2.1.trans (centralizer_le he.ge),he,hh.1⟩

include e hz hn in
set_option maxHeartbeats 500000 in
/-- The original restricted radical supplies the literal chain and the
reverse whole-core/omega estimates, with its generating edge and transporter.
No extra kernel normalization or small-critical-image premise is assumed. -/
theorem original_radical_reverse_omega_knownSimple
    (hb : 6 < replacementDistance h d)
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
        (t : BackwardShift (h := h) r.path) (v : BackwardShift (h := h) t.path)
        (w : BackwardShift (h := h) v.path),
      SylowTerminalPath.OrbitPrefix (h := h) r.path (replacementDistance h d) ∧
      act d.radical v.transporter (t.path.walk.getVert 1) = v.edge ∧
      (SmallMover.join (U d.radical v.start) (Q d.radical v.start) (Q d.radical v.edge) 4 ≠
        SmallMover.join (U d.radical t.start) (Q d.radical t.start) (Q d.radical v.edge) 4 →
        let z := v.path.walk.getVert (v.path.walk.length-2)
        ∃ p' : CriticalPath d.radical (replacementGeometry h d) z w.start,
          (∀ i, p'.walk.getVert i = w.path.walk.getVert (w.path.walk.length-i)) ∧
          ∃ b : BackwardShift (h := h) p',
            act d.radical b.transporter (p'.walk.getVert 1) = b.edge ∧
            let H := ⁅Z d.radical b.start,Z d.radical v.start⁆
            Nat.card H = 2 ∧ H ≤ X d.radical z ∧
            ∀ b' : BackwardShift (h := h) p',
              let E := SmallMover.join (U d.radical b'.start) (Q d.radical b'.start)
                (Q d.radical b'.edge) 4
              Q d.radical z ≤ E ∧ E ≤ centralizer (H : Set (FreeAmalgam d.radical)) ∧
              ⁅Z d.radical b'.start,Z d.radical v.start⁆ = H ∧
              ¬ Z d.radical b'.start ⊓ Q d.radical v.start ≤
                B d.radical z ((replacementGeometry h d).Z_normal _)) := by
  have hb4 : 4 < replacementDistance h d := by omega
  obtain ⟨q₀,hqe,hqT,hqgen,c,c',p₀,hchain,q,r,t,v,hr,hv⟩ :=
    original_four_shift_witness (G := G) (L := L) (R := R)
      (h := h) (e := e) (hz := hz) (hn := hn) (d := d) (a' := a') hb4 hcard p hfirst
  refine ⟨q₀,hqe,hqT,hqgen,c,c',p₀,hchain,q,r,t,v,?_⟩
  apply select_backward_property (h := h) (e := e) (hz := hz) (hn := hn) hb4 hcard v.path
  intro w
  refine ⟨hr,hv,?_⟩
  intro hne
  exact five_shift_reverse_omega_knownSimple (h := h) (e := e) (hz := hz) (hn := hn)
    hb hcard p₀ q r t v w hr hv hne


end AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
