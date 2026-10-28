module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.SylowCoreSaturation

public noncomputable section
/-!
Reverse the fifth backward shift in the distance greater than six branch.

This is the literal shifted-path comparison used in MS93 (5.10)--(5.11),
printed pp. 922--923.  The original radical, transporter and both possible
cover orders are retained throughout; no exceptional graph is identified with
this natural graph.
-/
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

private theorem retarget_criticalPath {x y y' : Vertex d.radical}
    (cp : CriticalPath d.radical (replacementGeometry h d) x y) (hy : y = y') :
    ∃ cp' : CriticalPath d.radical (replacementGeometry h d) x y',
      ∀ i, cp'.walk.getVert i = cp.walk.getVert i := by
  subst y'
  exact ⟨cp,fun _ => rfl⟩

private theorem reversed_critical_path (s : FullSymmetricAction h e hz hn d)
    (hc : DistanceTwo.CentralLayer d) {x y : Vertex d.radical}
    (cp : CriticalPath d.radical (replacementGeometry h d) x y) :
    ∃ cp' : CriticalPath d.radical (replacementGeometry h d) y x,
      ∀ i, cp'.walk.getVert i = cp.walk.getVert (cp.walk.length-i) := by
  refine ⟨⟨cp.end_color,cp.walk.reverse,
    by rw [SimpleGraph.Walk.length_reverse,cp.shortest,SimpleGraph.dist_comm],
    critical_reverse_pair s hc cp⟩,?_⟩
  intro i
  exact SimpleGraph.Walk.getVert_reverse _ _

include h in
/-- A backward shift of the literal reversed second shift ends at the
intermediate start. Its seed lies in the earlier whole core and, beyond
six, centralizes the earlier critical endpoint. -/
theorem reverse_backward_seed_locations
    (hb : 6 < replacementDistance h d) {a a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a a')
    (q : BackwardShift (h := h) p) (r : BackwardShift (h := h) q.path)
    (p' : CriticalPath d.radical (replacementGeometry h d)
      (q.path.walk.getVert (q.path.walk.length-2)) r.start)
    (hrev : ∀ i, p'.walk.getVert i = r.path.walk.getVert (r.path.walk.length-i))
    (b : BackwardShift (h := h) p') :
    ∃ cp : CriticalPath d.radical (replacementGeometry h d) b.start q.start,
      (∀ i, cp.walk.getVert i = b.path.walk.getVert i) ∧
      Z d.radical b.start ≤ Q d.radical a ∧
      Z d.radical b.start ≤ centralizer (Z d.radical a' : Set (FreeAmalgam d.radical)) := by
  have hp : p.walk.length = replacementDistance h d := p.length_eq_b
  have hq : q.path.walk.length = replacementDistance h d := q.path.length_eq_b
  have hr : r.path.walk.length = replacementDistance h d := r.path.length_eq_b
  have hp' : p'.walk.length = replacementDistance h d := p'.length_eq_b
  have hbl : b.path.walk.length = replacementDistance h d := b.path.length_eq_b
  have hr2 : r.path.walk.getVert 2 = q.start := by
    simpa only [Nat.zero_add,SimpleGraph.Walk.getVert_zero] using r.overlap 0 (Nat.zero_le _)
  have hq2 : q.path.walk.getVert 2 = a := by
    simpa only [Nat.zero_add,SimpleGraph.Walk.getVert_zero] using q.overlap 0 (Nat.zero_le _)
  have hpre : p'.walk.getVert (p'.walk.length-2) = q.start := by
    rw [hrev,show r.path.walk.length-(p'.walk.length-2)=2 by omega,hr2]
  have hcp := retarget_criticalPath (h := h) b.path hpre
  obtain ⟨cp,hcp⟩ := hcp
  have hloc : b.path.walk.getVert (b.path.walk.length-2) = a := by
    calc
      b.path.walk.getVert (b.path.walk.length-2) =
          b.path.walk.getVert (replacementDistance h d-4+2) := congrArg _ (by omega)
      _ = p'.walk.getVert (replacementDistance h d-4) := b.overlap _ (by omega)
      _ = r.path.walk.getVert (r.path.walk.length-(replacementDistance h d-4)) := hrev _
      _ = r.path.walk.getVert 4 := congrArg _ (by omega)
      _ = q.path.walk.getVert 2 := r.overlap 2 (by omega)
      _ = a := hq2
  have hseed : Z d.radical b.start ≤ Q d.radical a := by
    have hd : (cosetGraph d.radical).dist b.start a = b.path.walk.length-2 := by
      calc
        (cosetGraph d.radical).dist b.start a =
            (cosetGraph d.radical).dist b.start (b.path.walk.getVert (b.path.walk.length-2)) :=
          congrArg (fun x => (cosetGraph d.radical).dist b.start x) hloc.symm
        _ = _ := b.path.dist_start (Nat.sub_le _ _)
    apply Z_le_Q_of_dist_lt d.radical b.start
      ((replacementGeometry h d).exists_critical b.start b.path.start_color)
    rw [(replacementGeometry h d).distance_constant b.start b.path.start_color,hd]
    change b.path.walk.length-2 < replacementDistance h d
    omega
  let z := q.path.walk.getVert (q.path.walk.length-2)
  have hb2 : (cosetGraph d.radical).dist b.start z = 2 := by
    have hh : b.path.walk.getVert 2 = z := by
      simpa only [Nat.zero_add,SimpleGraph.Walk.getVert_zero] using b.overlap 0 (Nat.zero_le _)
    exact (congrArg (fun x => (cosetGraph d.radical).dist b.start x) hh).symm.trans
      (b.path.dist_start (by omega))
  have hz2 : (cosetGraph d.radical).dist z (p.walk.getVert (p.walk.length-2)) = 2 := by
    change (cosetGraph d.radical).dist (q.path.walk.getVert (q.path.walk.length-2))
      (p.walk.getVert (p.walk.length-2)) = 2
    rw [q.path.dist_end]
    omega
  have ha2 : (cosetGraph d.radical).dist (p.walk.getVert (p.walk.length-2)) a' = 2 := by
    rw [p.dist_end]
    omega
  have hza : (cosetGraph d.radical).dist z a' ≤ 4 := by
    have hh := (cosetGraph_connected d.radical).dist_triangle
      (u := z) (v := p.walk.getVert (p.walk.length-2)) (w := a')
    omega
  have hba : (cosetGraph d.radical).dist b.start a' ≤ 6 := by
    have hh := (cosetGraph_connected d.radical).dist_triangle (u := b.start) (v := z) (w := a')
    omega
  have hseed' : Z d.radical b.start ≤ Q d.radical a' := by
    apply Z_le_Q_of_dist_lt d.radical b.start
      ((replacementGeometry h d).exists_critical b.start b.path.start_color)
    rw [(replacementGeometry h d).distance_constant b.start b.path.start_color]
    exact lt_of_le_of_lt hba hb
  exact ⟨cp,hcp,hseed,hseed'.trans (le_centralizer_iff.mp
    (commutator_eq_bot_iff_le_centralizer.mp (Z_centralizes_Q d.radical a' p.end_color)))⟩

include e hz hn in
/-- Beyond six, the actual reverse backward seeds satisfy the core and
fixedness conditions of the two-seed comparison. Both critical paths remain
literal; the common line is taken at the intermediate seed. -/
theorem five_shift_reverse_seed_comparison_knownSimple
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
        Nat.card (⁅Z d.radical b.start,Z d.radical v.start⁆ : Subgroup (FreeAmalgam d.radical)) = 2 ∧
        X d.radical w.start ≤ normalizer
          (((Z d.radical b.start ⊓ Q d.radical v.start) ⊔ Z d.radical z :
            Subgroup (FreeAmalgam d.radical)) : Set (FreeAmalgam d.radical)) ∧
        ∀ b' : BackwardShift (h := h) p',
          (Q d.radical v.start).relIndex
            (Q d.radical v.start ⊔ (Z d.radical b.start ⊔ Z d.radical b'.start)) = 2 ∧
          ⁅Z d.radical b.start,Z d.radical v.start⁆ = ⁅Z d.radical b'.start,Z d.radical v.start⁆ := by
  have hb4 : 4 < replacementDistance h d := by omega
  have hb2 : 2 < replacementDistance h d := by omega
  let s := fullSymmetricAction_knownSimple h e hz hn d hb2
  have hc := DistanceTwo.centralLayer_knownSimple G L R h e hz hn d
  let z := v.path.walk.getVert (v.path.walk.length-2)
  have hex : ∃ p' : CriticalPath d.radical (replacementGeometry h d) z w.start,
      ∀ i, p'.walk.getVert i = w.path.walk.getVert (w.path.walk.length-i) :=
    reversed_critical_path s hc w.path
  obtain ⟨p',hrev⟩ := hex
  have hchoice : ∃ b : BackwardShift (h := h) p',
      act d.radical b.transporter (p'.walk.getVert 1) = b.edge :=
    SylowShiftChain.backwardShift_with_edge (h := h) (e := e) (hz := hz) (hn := hn)
      (d := d) (a := z) (a' := w.start) hb4 hcard p'
  obtain ⟨b,hbact⟩ := hchoice
  have hlocs : ∃ cp : CriticalPath d.radical (replacementGeometry h d) b.start v.start,
      (∀ i, cp.walk.getVert i = b.path.walk.getVert i) ∧
      Z d.radical b.start ≤ Q d.radical t.start ∧
      Z d.radical b.start ≤ centralizer (Z d.radical (r.path.walk.getVert (r.path.walk.length-2)) :
        Set (FreeAmalgam d.radical)) :=
    reverse_backward_seed_locations (h := h) (d := d)
      (a := t.start) (a' := r.path.walk.getVert (r.path.walk.length-2)) hb t.path v w p' hrev b
  obtain ⟨cp,hcp,hQ,hC⟩ := hlocs
  have hpair (b' : BackwardShift (h := h) p') :
      (Q d.radical v.start).relIndex
        (Q d.radical v.start ⊔ (Z d.radical b.start ⊔ Z d.radical b'.start)) = 2 ∧
      Nat.card (⁅Z d.radical b.start,Z d.radical v.start⁆ : Subgroup (FreeAmalgam d.radical)) = 2 ∧
      ⁅Z d.radical b.start,Z d.radical v.start⁆ = ⁅Z d.radical b'.start,Z d.radical v.start⁆ := by
    have hlocs' : ∃ cp' : CriticalPath d.radical (replacementGeometry h d) b'.start v.start,
        (∀ i, cp'.walk.getVert i = b'.path.walk.getVert i) ∧
        Z d.radical b'.start ≤ Q d.radical t.start ∧
        Z d.radical b'.start ≤ centralizer (Z d.radical (r.path.walk.getVert (r.path.walk.length-2)) :
          Set (FreeAmalgam d.radical)) :=
      reverse_backward_seed_locations (h := h) (d := d)
        (a := t.start) (a' := r.path.walk.getVert (r.path.walk.length-2)) hb t.path v w p' hrev b'
    obtain ⟨cp',hcp',hQ',hC'⟩ := hlocs'
    exact four_shift_terminal_seed_pair_knownSimple (h := h) (e := e) (hz := hz) (hn := hn) hb4 hcard p q r t v hr hv hne cp cp' hQ hQ' hC hC'
  refine ⟨p',hrev,b,hbact,(hpair b).2.1,?_,fun b' => ⟨(hpair b').1,(hpair b').2.2⟩⟩
  have hgen := four_shift_unequal_omega_not_centrally_generated_knownSimple
    (h := h) (e := e) (hz := hz) (hn := hn) hb4 hcard p q r t v hr hv hne w.start w.path.start_color
  have hs₀ := SylowShiftChain.two_backward_shifts_small_moving_knownSimple
    (e := e) (hz := hz) (hn := hn) hb4 t.path v w
  have hs : (Q d.radical z).relIndex (Z d.radical w.start) < 4 := by rw [hs₀.2.1]; decide
  have hs' : (Q d.radical w.start).relIndex (Z d.radical z) < 4 := by
    rw [(small_critical_indices s hc w.path hs).2]; decide
  have hnorm := backward_full_omega_normalization_of_not_centrally_generated s hc hb2 p' hs' b hgen
  have hpre : p'.walk.getVert (p'.walk.length-2) = v.start := by
    rw [hrev]
    have hl : w.path.walk.length = replacementDistance h d := w.path.length_eq_b
    have hl' : p'.walk.length = replacementDistance h d := p'.length_eq_b
    rw [show w.path.walk.length-(p'.walk.length-2)=2 by omega]
    simpa only [Nat.zero_add,SimpleGraph.Walk.getVert_zero] using w.overlap 0 (Nat.zero_le _)
  rwa [hpre] at hnorm

include e hz hn in
private theorem select_backward_property
    (hb : 4 < replacementDistance h d)
    (hcard : Nat.card (d.radical.map (SourceReduction.projection h e hz hn d)) = 16)
    {a a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a a')
    (P : BackwardShift (h := h) p → Prop) (hP : ∀ w, P w) : ∃ w, P w := by
  obtain ⟨w,_⟩ := SylowShiftChain.backwardShift_with_edge
    (h := h) (e := e) (hz := hz) (hn := hn) hb hcard p
  exact ⟨w,hP w⟩

include e hz hn in
private theorem original_four_shift_witness
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
      act d.radical v.transporter (t.path.walk.getVert 1) = v.edge := by
  obtain ⟨q₀,hqe,hqT,hqgen,c,c',p₀,hchain,q,r,t,v,hr,hv,_⟩ :=
    original_radical_terminal_core_product_knownSimple hb hcard p hfirst
  exact ⟨q₀,hqe,hqT,hqgen,c,c',p₀,hchain,q,r,t,v,hr,hv⟩

include e hz hn in
set_option maxHeartbeats 500000 in
/-- The literal original radical constructs the fifth shift and the reverse
seed comparison beyond distance six. No core-containment, endpoint-fixedness,
small-critical-image or omega-generation premise is supplied by the caller. -/
theorem original_radical_reverse_seed_comparison_knownSimple
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
            Nat.card (⁅Z d.radical b.start,Z d.radical v.start⁆ : Subgroup (FreeAmalgam d.radical)) = 2 ∧
            X d.radical w.start ≤ normalizer
              (((Z d.radical b.start ⊓ Q d.radical v.start) ⊔ Z d.radical z :
                Subgroup (FreeAmalgam d.radical)) : Set (FreeAmalgam d.radical)) ∧
            ∀ b' : BackwardShift (h := h) p',
              (Q d.radical v.start).relIndex
                (Q d.radical v.start ⊔ (Z d.radical b.start ⊔ Z d.radical b'.start)) = 2 ∧
              ⁅Z d.radical b.start,Z d.radical v.start⁆ = ⁅Z d.radical b'.start,Z d.radical v.start⁆) := by
  have hb4 : 4 < replacementDistance h d := by omega
  obtain ⟨q₀,hqe,hqT,hqgen,c,c',p₀,hchain,q,r,t,v,hr,hv⟩ :=
    original_four_shift_witness (G := G) (L := L) (R := R)
      (h := h) (e := e) (hz := hz) (hn := hn) (d := d) (a' := a') hb4 hcard p hfirst
  refine ⟨q₀,hqe,hqT,hqgen,c,c',p₀,hchain,q,r,t,v,?_⟩
  apply select_backward_property (h := h) (e := e) (hz := hz) (hn := hn) hb4 hcard v.path
  intro w
  refine ⟨hr,hv,?_⟩
  intro hne
  exact five_shift_reverse_seed_comparison_knownSimple (h := h) (e := e) (hz := hz) (hn := hn)
    hb hcard p₀ q r t v w hr hv hne

end AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
