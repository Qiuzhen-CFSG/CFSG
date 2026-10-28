module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.SylowShiftChain
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.SylowTrappedExclusion
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.ElementaryKernelControl

/-!
# Restricted terminal kernels on the image-sixteen shift chain

For an elementary subgroup of the starting radius trapped in the predecessor
core, failure of endpoint normalization forces its kernel displacement to be
an aligned line of order two. The estimate applies to the actual hyperplane
of the last backward seed, without treating a whole selected span as elementary.

On three constructed shifts that hyperplane escapes the intermediate Baumann
slice. The last small mover normalizes its join with the intermediate seed,
whereas the intermediate residual does not. Endpoint normalization therefore
forces core containment; central generation of full omega then forces equality
of the two small movers. In the nonnormalizing branch, the full critical kernel
normalizes the hyperplane, so the omega alternative gives central generation
at every component vertex and the exact full/seed/moving displacement identities.

The final consumer constructs all three shifts from the literal original MS
radical and retains its conjugation map and generating edge. Both moving covers
and all central attachments are retained. The central-intersection contradiction
in (5.10), its mover iteration, (5.11), image eight and distance four still require
independent arguments within the large-distance proof.

Source: Meierfrankenfeld--Stellmacher, Pushing up weak BN-pairs of rank two
(1993), (3.3), (5.5)(c), (5.9)--(5.10), printed pp.866--867,915,921--923.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender BinaryPermutation
open scoped commutatorElement Pointwise IsMulCommutative
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.SylowTerminalKernel
universe u
variable {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
  {h : SmallMSPair KnownSimple.IsKnownSimple L R} {e : CentralMarking L}
  {hz : center (L ⧸ pCore 2 L) = ⊥} {hn : InitialNatural h e hz}
  {d : Replacement L R}

include e hz hn in
/-- The actual restricted seed, not necessarily a full neighboring seed,
has a nonzero aligned kernel commutator when the critical endpoint fails
to normalize its join with the starting seed. -/
theorem restricted_seed_kernel_line_knownSimple
    (hb : 4 < replacementDistance h d)
    {a z : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a z)
    (hsmall : (Q d.radical z).relIndex (Z d.radical a) < 4)
    (Y : Subgroup (FreeAmalgam d.radical)) (hYel : IsElementaryAbelian 2 Y)
    (hCV : Y ≤ V d.radical a)
    (htrap : Y ≤ Q d.radical (p.walk.getVert (p.walk.length-2)))
    (hYN : Z d.radical z ⊓ Q d.radical a ≤ normalizer (Y : Set (FreeAmalgam d.radical)))
    (hnorm : ¬ Z d.radical z ≤ normalizer
      ((Y ⊔ Z d.radical a : Subgroup (FreeAmalgam d.radical)) : Set (FreeAmalgam d.radical))) :
    let K := ⁅Y,Z d.radical z ⊓ Q d.radical a⁆
    Nat.card K = 2 ∧ K ≤ Y ∧
      K ≤ ⁅Z d.radical a,Z d.radical z⁆ ⊔
        (Z d.radical z ⊓ centralizer (stabilizer d.radical z : Set (FreeAmalgam d.radical))) := by
  have hb2 : 2 < replacementDistance h d := by omega
  let s := fullSymmetricAction_knownSimple h e hz hn d hb2
  have hc := DistanceTwo.centralLayer_knownSimple G L R h e hz hn d
  let F := Z d.radical z ⊓ Q d.radical a
  let P := Y ⊔ Z d.radical a
  let K := ⁅Y,F⁆
  have hlast := critical_last_edge_inputs (h := h) hb2 p
  have hfixed := critical_full_kernel_eq s hc p
  have hAV : Z d.radical a ≤ V d.radical a := Z_le_VBall d.radical a 2
  have hVV : V d.radical a ≤ centralizer (V d.radical a : Set (FreeAmalgam d.radical)) :=
    le_centralizer_iff_isMulCommutative.mpr (V_abelian_of_four_lt d.radical p.start_color hb)
  have hAC : Z d.radical a ≤ centralizer (Y : Set (FreeAmalgam d.radical)) :=
    hAV.trans (hVV.trans (centralizer_le hCV))
  have hAF : Z d.radical a ≤ centralizer (F : Set (FreeAmalgam d.radical)) :=
    (commutator_eq_bot_iff_le_centralizer.mp (Z_centralizes_Q d.radical a p.start_color)).trans
      (centralizer_le inf_le_right)
  have hPF : ⁅P,F⁆ = K := elementary_commutator_sup_central
    (Y) (Z d.radical a) F (hAC.trans (Subgroup.centralizer_le_normalizer _)) hAF
  let := (replacementGeometry h d).Z_elementary (replacementDistance_pos h d) a p.start_color
  let := hYel
  have hel : IsElementaryAbelian 2 P := IsElementaryAbelian.sup_of_le_centralizer hAC
  have hPt : P ≤ Q d.radical (p.walk.getVert (p.walk.length-1)) :=
    sup_le (htrap.trans hlast.2.1) hlast.2.2
  have hindex : (centralizer (Z d.radical a : Set (FreeAmalgam d.radical))).relIndex
      (U d.radical z) ≤ 2 := by
    let := finite_Z d.radical z
    let : Finite (U d.radical z) := Finite.of_injective
      (inclusion (DistanceEight.U_le_Z d.radical z)) (inclusion_injective _)
    have hQC : Q d.radical a ≤ centralizer (Z d.radical a : Set (FreeAmalgam d.radical)) :=
      le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp
        (Z_centralizes_Q d.radical a p.start_color))
    exact ((relIndex_le_of_le_left hQC index_ne_zero_of_finite).trans
      (relIndex_le_of_le_right (DistanceEight.U_le_Z d.radical z) index_ne_zero_of_finite)).trans_eq
        (small_critical_indices s hc p hsmall).2
  have hKC : K ≤ Y := le_normalizer_iff_commutator_le_left.mp hYN
  have hcrit : ⁅Z d.radical z,Z d.radical a⁆ ≤ Z d.radical a := by
    rw [commutator_comm]
    exact ((critical_Z_commutator_le_moving (h := h) p).trans inf_le_left).trans
      (DistanceEight.U_le_Z d.radical a)
  have hfail : ¬ ⁅Z d.radical z,P⁆ ≤
      ⁅Z d.radical z ⊓ centralizer (Z d.radical a : Set (FreeAmalgam d.radical)),P⁆ ⊔
        ⁅Z d.radical z,Z d.radical a⁆ := by
    intro hh
    rw [←hfixed,commutator_comm F P,hPF] at hh
    apply hnorm
    exact le_normalizer_iff_commutator_le_right.mpr
      (hh.trans (sup_le (hKC.trans le_sup_left) (hcrit.trans le_sup_right)))
  have hcontrol := elementary_edge_kernel_small_aligned s hc p.end_color hlast.1
    (Z d.radical a) P hlast.2.2 hPt le_sup_right hel p.critical.2 hindex hfail
  rw [←hfixed,commutator_comm F P,hPF] at hcontrol
  have hCG : Y ≤ stabilizer d.radical z :=
    (htrap.trans hlast.2.1).trans (fun _ hx => hx.2 _ (adjacent_symm d.radical hlast.1))
  have hne : K ≠ ⊥ := by
    intro hzero
    have hmove := small_critical_kernel_commutator s hc p hsmall Y hCG
      (commutator_eq_bot_iff_le_centralizer.mp hzero)
    have hcrit' : ⁅Z d.radical a,Z d.radical z⁆ ≤ Z d.radical a := by
      rw [commutator_comm]
      exact hcrit
    have htotal := commutator_sup_le_of_relative_normal (stabilizer d.radical a)
      Y (Z d.radical a) (Z d.radical z) (Z d.radical a) (Z_normalized d.radical a)
      (hCV.trans ((replacementGeometry h d).V_local a p.start_color (by
        rw [(replacementGeometry h d).distance_constant a p.start_color]; exact hb2)))
      (Z_le_stabilizer d.radical a) (hmove.trans hcrit') hcrit'
    exact hnorm (le_normalizer_iff_commutator_le_left.mpr (htotal.trans le_sup_right))
  let := finite_stabilizer d.radical a
  let : Finite Y := Finite.of_injective
    (inclusion (hCV.trans ((replacementGeometry h d).V_local a p.start_color (by
      rw [(replacementGeometry h d).distance_constant a p.start_color]; exact hb2))))
    (inclusion_injective _)
  let : Finite K := Finite.of_injective (inclusion hKC) (inclusion_injective _)
  have hpos : 1 < Nat.card K := (one_lt_card_iff_ne_bot K).mpr hne
  have hbound : Nat.card K ≤ 2 := hcontrol.1
  change Nat.card K = 2 ∧ _
  refine ⟨by omega,hKC,?_⟩
  simpa only [commutator_comm (Z d.radical z) (Z d.radical a)] using hcontrol.2

include e hz hn in
/-- Failure to normalize the actual restricted last kernel forces central
generation of full omega at every component vertex. The full, seed and
 moving critical kernels have identical displacement on the predecessor core. -/
theorem three_shift_nonnormalized_full_kernel_knownSimple
    (hb : 4 < replacementDistance h d)
    {a a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a a')
    (q : BackwardShift (h := h) p) (r : BackwardShift (h := h) q.path)
    (t : BackwardShift (h := h) r.path)
    (hnorm : ¬ Z d.radical (q.path.walk.getVert (q.path.walk.length-2)) ≤ normalizer
      (((Z d.radical t.start ⊓ Q d.radical (r.path.walk.getVert (r.path.walk.length-2))) ⊔
        Z d.radical r.start : Subgroup (FreeAmalgam d.radical)) : Set (FreeAmalgam d.radical))) :
    let z := q.path.walk.getVert (q.path.walk.length-2)
    let v := r.path.walk.getVert (r.path.walk.length-2)
    (∀ w : Vertex d.radical, color d.radical w = false →
      X d.radical w = U d.radical w ⊔
        (X d.radical w ⊓ centralizer (stabilizer d.radical w : Set (FreeAmalgam d.radical)))) ∧
    X d.radical z ⊓ Q d.radical r.start = (Z d.radical z ⊓ Q d.radical r.start) ⊔
      (X d.radical z ⊓ centralizer (stabilizer d.radical z : Set (FreeAmalgam d.radical))) ∧
    ∀ Y : Subgroup (FreeAmalgam d.radical), Y ≤ Q d.radical v →
      ⁅Y,X d.radical z ⊓ Q d.radical r.start⁆ = ⁅Y,Z d.radical z ⊓ Q d.radical r.start⁆ ∧
      ⁅Y,X d.radical z ⊓ Q d.radical r.start⁆ = ⁅Y,U d.radical z ⊓ Q d.radical r.start⁆ := by
  have hb2 : 2 < replacementDistance h d := by omega
  let s := fullSymmetricAction_knownSimple h e hz hn d hb2
  have hc := DistanceTwo.centralLayer_knownSimple G L R h e hz hn d
  let z := q.path.walk.getVert (q.path.walk.length-2)
  let v := r.path.walk.getVert (r.path.walk.length-2)
  let K := Z d.radical t.start ⊓ Q d.radical v
  have hd := SylowShiftChain.two_backward_shifts_small_moving_knownSimple
    (e := e) (hz := hz) (hn := hn) hb p q r
  have hsmall : (Q d.radical z).relIndex (Z d.radical r.start) < 4 := by
    rw [hd.2.1]; decide
  have htcol : color d.radical t.edge = true := by
    have hh := adjacent_color_ne d.radical t.adjacent_start
    rw [r.path.start_color] at hh
    cases he : color d.radical t.edge <;> simp_all
  have hzv : (cosetGraph d.radical).dist z v = 2 := by
    rw [SimpleGraph.dist_comm,r.path.dist_end]
    have hl : r.path.walk.length = replacementDistance h d := r.path.length_eq_b
    omega
  have hXG : X d.radical z ⊓ Q d.radical r.start ≤ stabilizer d.radical t.start :=
    (inf_le_right.trans (Q_le_adjacent_h d.radical htcol t.adjacent_start)).trans
      (fun _ hx => hx.2 _ (adjacent_symm d.radical t.adjacent_shift))
  have hXv : X d.radical z ⊓ Q d.radical r.start ≤ stabilizer d.radical v :=
    ((inf_le_left.trans (omegaCenter_le (Q d.radical z))).trans
      (Q_le_stabilizer_of_dist_two d.radical z v r.path.end_color hzv))
  have hNK : X d.radical z ⊓ Q d.radical r.start ≤ normalizer (K : Set (FreeAmalgam d.radical)) :=
    (le_inf (hXG.trans (Z_normalized d.radical t.start))
      (hXv.trans (Q_normalized d.radical v))).trans inf_normalizer_le_normalizer_inf
  have hKQ : K ≤ Q d.radical r.start :=
    (inf_le_left.trans (neighbor_seed_le_radius t.adjacent_start t.adjacent_shift)).trans
      ((replacementGeometry h d).V_le_Q hb2 r.start r.path.start_color)
  have hlast := critical_last_edge_inputs (h := h) hb2 r.path
  have hvG : Q d.radical v ≤ stabilizer d.radical z :=
    hlast.2.1.trans (fun _ hx => hx.2 _ (adjacent_symm d.radical hlast.1))
  have hgen : X d.radical z = U d.radical z ⊔
      (X d.radical z ⊓ centralizer (stabilizer d.radical z : Set (FreeAmalgam d.radical))) := by
    rcases critical_X_generation_or_normalization s hc r.path hsmall K
      (inf_le_right.trans hvG) hKQ hNK with hh | hh
    · exact hh
    · have hZX : Z d.radical z ≤ X d.radical z := by
        apply (replacementGeometry h d).omega_bound z r.path.end_color
        rw [(replacementGeometry h d).distance_constant z r.path.end_color]
        exact replacementDistance_pos h d
      exact (hnorm (hZX.trans hh)).elim
  refine ⟨X_central_generation_all r.path.end_color hgen,
    critical_X_kernel_of_central_generation s hc r.path hgen,?_⟩
  intro Y hY
  have he := (critical_X_displacements_of_central_generation s hc r.path hgen Y (hY.trans hvG)).2
  refine ⟨he,he.trans ?_⟩
  simpa only [commutator_comm Y] using
    (critical_kernel_predecessor_moving s hc hb2 r.path).2.2 Y hY


include e hz hn in
/-- In the actual three-shift configuration, the full last critical kernel
escapes the intermediate Baumann slice. Its join with the intermediate seed
is normalized by the last small mover, but not by the intermediate residual.
If the preceding critical endpoint normalizes the join, the intermediate
core must lie in that same small mover. Otherwise the literal double-kernel
commutator is a line aligned with the preceding critical commutator. -/
theorem three_shift_kernel_control_knownSimple
    (hb : 4 < replacementDistance h d)
    (hcard : Nat.card (d.radical.map (SourceReduction.projection h e hz hn d)) = 16)
    {a a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a a')
    (q : BackwardShift (h := h) p) (r : BackwardShift (h := h) q.path)
    (t : BackwardShift (h := h) r.path) :
    let z := q.path.walk.getVert (q.path.walk.length-2)
    let v := r.path.walk.getVert (r.path.walk.length-2)
    let K := Z d.radical t.start ⊓ Q d.radical v
    let N := K ⊔ Z d.radical r.start
    let E := SmallMover.join (U d.radical t.start) (Q d.radical t.start) (Q d.radical t.edge) 4
    K.relIndex (Z d.radical t.start) = 2 ∧
      (¬ K ≤ B d.radical r.start ((replacementGeometry h d).Z_normal _)) ∧
      E ≤ normalizer (N : Set (FreeAmalgam d.radical)) ∧
      (¬ Ltilde d.radical r.start ≤ normalizer (N : Set (FreeAmalgam d.radical))) ∧
      (Z d.radical z ≤ normalizer (N : Set (FreeAmalgam d.radical)) →
        Q d.radical r.start ≤ E ∧
        (X d.radical r.start = U d.radical r.start ⊔
          (X d.radical r.start ⊓ centralizer (stabilizer d.radical r.start : Set (FreeAmalgam d.radical))) →
          E = SmallMover.join (U d.radical r.start) (Q d.radical r.start) (Q d.radical t.edge) 4)) ∧
      ((¬ Z d.radical z ≤ normalizer (N : Set (FreeAmalgam d.radical))) →
        let H := ⁅K,Z d.radical z ⊓ Q d.radical r.start⁆
        Nat.card H = 2 ∧ H ≤ K ∧
          H ≤ ⁅Z d.radical r.start,Z d.radical z⁆ ⊔
            (Z d.radical z ⊓ centralizer (stabilizer d.radical z : Set (FreeAmalgam d.radical)))) := by
  have hb2 : 2 < replacementDistance h d := by omega
  let s := fullSymmetricAction_knownSimple h e hz hn d hb2
  have hc := DistanceTwo.centralLayer_knownSimple G L R h e hz hn d
  let z := q.path.walk.getVert (q.path.walk.length-2)
  let v := r.path.walk.getVert (r.path.walk.length-2)
  let K := Z d.radical t.start ⊓ Q d.radical v
  let N := K ⊔ Z d.radical r.start
  let E := SmallMover.join (U d.radical t.start) (Q d.radical t.start) (Q d.radical t.edge) 4
  have hr := SylowShiftChain.two_backward_shifts_small_moving_knownSimple
    (e := e) (hz := hz) (hn := hn) hb p q r
  have ht := SylowShiftChain.two_backward_shifts_small_moving_knownSimple
    (e := e) (hz := hz) (hn := hn) hb q.path r t
  have hrs : (Q d.radical z).relIndex (Z d.radical r.start) < 4 := by rw [hr.2.1]; decide
  have hts : (Q d.radical v).relIndex (Z d.radical t.start) < 4 := by rw [ht.2.1]; decide
  have hki : K.relIndex (Z d.radical t.start) = 2 := by
    rw [show K = Z d.radical t.start ⊓ Q d.radical v from rfl,inf_relIndex_left]
    exact ht.2.1
  have hstrict : 2 < (B d.radical r.start ((replacementGeometry h d).Z_normal _)).relIndex
      (U d.radical t.start) := by
    have hh := SylowForwardSpan.sixteen_small_forward_slice_strict_at_knownSimple
      (e := e) (hz := hz) (hn := hn) hb hcard r.path hrs
    have hm : (B d.radical r.start ((replacementGeometry h d).Z_normal _)).map
        (MulAut.conj t.transporter⁻¹).toMonoidHom =
          B d.radical r.start ((replacementGeometry h d).Z_normal _) :=
      mem_normalizer_iff_map_conj_eq.mp (Escape.Propagation.Rigidity.B_normalized
        (geometry := replacementGeometry h d) hb2 r.start r.path.start_color
        ((stabilizer d.radical r.start).inv_mem t.transporter_mem))
    rw [←t.start_eq,U_act,←hm,relIndex_map_map_of_injective _ _ (MulAut.conj _).injective]
    exact hh
  let := finite_Z d.radical t.start
  have hnot : ¬ K ≤ B d.radical r.start ((replacementGeometry h d).Z_normal _) := by
    intro hKB
    have hi : (B d.radical r.start ((replacementGeometry h d).Z_normal _)).relIndex
        (Z d.radical t.start) ≤ 2 :=
      (relIndex_le_of_le_left hKB index_ne_zero_of_finite).trans_eq hki
    have hj := relIndex_le_of_le_right (H := B d.radical r.start ((replacementGeometry h d).Z_normal _))
      (DistanceEight.U_le_Z d.radical t.start) index_ne_zero_of_finite
    exact (Nat.not_le_of_gt hstrict) (hj.trans hi)
  have hfix := SylowTrappedMover.sixteen_common_kernel_centralizer_knownSimple
    (e := e) (hz := hz) (hn := hn) hb hcard t.path hts ht.2.2.2.2
  dsimp only at hfix
  rw [t.first] at hfix
  have hEK : E ≤ normalizer (K : Set (FreeAmalgam d.radical)) :=
    hfix.2.2.1.symm.le.trans inf_le_right
  have hET : E ≤ Q d.radical t.edge := SmallMover.join_le _ _ _ _
  have hTa : Q d.radical t.edge ≤ stabilizer d.radical r.start :=
    fun _ hx => hx.2 _ (adjacent_symm d.radical t.adjacent_start)
  have hEN : E ≤ normalizer (N : Set (FreeAmalgam d.radical)) :=
    (le_inf hEK ((hET.trans hTa).trans (Z_normalized d.radical r.start))).trans
      (normalizer_inf_normalizer_le_normalizer_sup _ _)
  have hZV : Z d.radical t.start ≤ V d.radical r.start :=
    neighbor_seed_le_radius t.adjacent_start t.adjacent_shift
  have hNV : N ≤ V d.radical r.start := sup_le (inf_le_left.trans hZV) (Z_le_VBall d.radical r.start 2)
  have hVG : V d.radical r.start ≤ stabilizer d.radical r.start :=
    (replacementGeometry h d).V_local r.start r.path.start_color (by
      rw [(replacementGeometry h d).distance_constant r.start r.path.start_color]
      exact hb2)
  let := finite_stabilizer d.radical r.start
  let : Finite (Z d.radical t.start ⊔ Z d.radical r.start : Subgroup (FreeAmalgam d.radical)) :=
    Finite.of_injective (inclusion (sup_le (hZV.trans hVG) (Z_le_stabilizer d.radical r.start)))
      (inclusion_injective _)
  have hNi : (Z d.radical r.start).relIndex N ≤ 8 :=
    (relIndex_le_of_le_right (show N ≤ Z d.radical t.start ⊔ Z d.radical r.start from
      sup_le_sup inf_le_left le_rfl) index_ne_zero_of_finite).trans
        (SylowSpanSelection.adjacent_seed_span_index_le_eight
          (e := e) (hz := hz) (hn := hn) hb r.path.start_color t.adjacent_start t.adjacent_shift)
  have hres : ¬ Ltilde d.radical r.start ≤ normalizer (N : Set (FreeAmalgam d.radical)) := by
    intro hnN
    exact hnot (le_sup_left.trans (residual_small_radius_le_slice_knownSimple (e := e)
      hb2 r.path.start_color N hNV hnN hNi))
  refine ⟨hki,hnot,hEN,hres,?_,?_⟩
  · intro hnZ
    have hcore : Q d.radical r.start ≤ E := by
      by_contra hnQ
      have hg := sixteen_opposite_residual_of_core_not_le_knownSimple
        (e := e) (hz := hz) (hn := hn) hb hcard r.path.start_color
        t.adjacent_start t.adjacent_shift (Z d.radical z) t.generation hnQ
      exact hres (hg.2.trans (sup_le hEN hnZ))
    refine ⟨hcore,?_⟩
    intro hsplit
    by_contra hne
    exact sixteen_unequal_containing_core_not_centrally_generated_knownSimple
      (e := e) (hz := hz) (hn := hn) hb hcard r.path.start_color
      t.adjacent_start t.adjacent_shift hne hcore hsplit
  · intro hnZ
    let F := Z d.radical z ⊓ Q d.radical r.start
    have htcol : color d.radical t.edge = true := by
      have hh := adjacent_color_ne d.radical t.adjacent_start
      rw [r.path.start_color] at hh
      cases he : color d.radical t.edge <;> simp_all
    have hFT : F ≤ Q d.radical t.edge := inf_le_right.trans
      (Q_le_adjacent_h d.radical htcol t.adjacent_start)
    have hzv : (cosetGraph d.radical).dist z v = 2 := by
      rw [SimpleGraph.dist_comm,r.path.dist_end]
      have hl : r.path.walk.length = replacementDistance h d := r.path.length_eq_b
      omega
    have hFv : F ≤ Q d.radical v := inf_le_left.trans (Z_le_Q_of_dist_lt d.radical z
      ((replacementGeometry h d).exists_critical z r.path.end_color) (by
        rw [(replacementGeometry h d).distance_constant z r.path.end_color,hzv]
        exact hb2))
    have hD : ⁅Z d.radical t.start,Z d.radical v⁆ ≤ Z d.radical v :=
      ((critical_Z_commutator_le_moving (h := h) t.path).trans inf_le_right).trans
        (DistanceEight.U_le_Z d.radical v)
    have hFD : F ≤ centralizer ((⁅Z d.radical t.start,Z d.radical v⁆ :
        Subgroup (FreeAmalgam d.radical)) : Set _) :=
      hFv.trans ((le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp
        (Z_centralizes_Q d.radical v t.path.end_color))).trans (centralizer_le hD))
    have hFE : F ≤ E := (le_inf hFT hFD).trans_eq hfix.1
    have hFN : F ≤ normalizer (K : Set (FreeAmalgam d.radical)) := hFE.trans hEK
    let := (replacementGeometry h d).Z_elementary (replacementDistance_pos h d) t.start t.path.start_color
    exact restricted_seed_kernel_line_knownSimple (e := e) (hz := hz) (hn := hn)
      hb r.path hrs K (IsElementaryAbelian.of_le inf_le_left) (inf_le_left.trans hZV)
      inf_le_right hFN hnZ


/-- The restricted original MS radical supplies the first generating edge,
then two actual shifts supply the terminal kernel dichotomy. No mover,
normalizer, small critical-image or full-omega splitting premise is supplied
by the caller. The nonnormalizing alternative retains the central attachment
and the literal full/seed/moving displacement identities. -/
theorem original_radical_three_shift_kernel_dichotomy_knownSimple
    (hb : 4 < replacementDistance h d)
    (hcard : Nat.card (d.radical.map (SourceReduction.projection h e hz hn d)) = 16)
    {a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) a')
    (hfirst : p.walk.getVert 1 = beta d.radical) :
    let T := ((R.subgroupOf (L ⊔ R)).subgroupOf d.overgroup).map (embedM d.radical)
    ∃ (q : BackwardShift (h := h) p) (r : BackwardShift (h := h) q.path)
      (t : BackwardShift (h := h) r.path),
      act d.radical q.transporter (beta d.radical) = q.edge ∧
      T.map (MulAut.conj q.transporter⁻¹).toMonoidHom = Q d.radical q.edge ∧
      T.map (MulAut.conj q.transporter⁻¹).toMonoidHom ⊔ Z d.radical a' =
        stabilizer d.radical (alpha d.radical) ∧
      act d.radical r.transporter (q.path.walk.getVert 1) = r.edge ∧
      act d.radical t.transporter (r.path.walk.getVert 1) = t.edge ∧
      let z := q.path.walk.getVert (q.path.walk.length-2)
      let v := r.path.walk.getVert (r.path.walk.length-2)
      let K := Z d.radical t.start ⊓ Q d.radical v
      let N := K ⊔ Z d.radical r.start
      let E := SmallMover.join (U d.radical t.start) (Q d.radical t.start) (Q d.radical t.edge) 4
      K.relIndex (Z d.radical t.start) = 2 ∧
      (¬ K ≤ B d.radical r.start ((replacementGeometry h d).Z_normal _)) ∧
      E ≤ normalizer (N : Set (FreeAmalgam d.radical)) ∧
      (¬ Ltilde d.radical r.start ≤ normalizer (N : Set (FreeAmalgam d.radical))) ∧
      ((Z d.radical z ≤ normalizer (N : Set (FreeAmalgam d.radical)) ∧
        Q d.radical r.start ≤ E ∧
        (X d.radical r.start = U d.radical r.start ⊔
          (X d.radical r.start ⊓ centralizer (stabilizer d.radical r.start : Set (FreeAmalgam d.radical))) →
          E = SmallMover.join (U d.radical r.start) (Q d.radical r.start) (Q d.radical t.edge) 4)) ∨
      ((¬ Z d.radical z ≤ normalizer (N : Set (FreeAmalgam d.radical))) ∧
        let H := ⁅K,Z d.radical z ⊓ Q d.radical r.start⁆
        Nat.card H = 2 ∧ H ≤ K ∧
        H ≤ ⁅Z d.radical r.start,Z d.radical z⁆ ⊔
          (Z d.radical z ⊓ centralizer (stabilizer d.radical z : Set (FreeAmalgam d.radical))) ∧
        (∀ w : Vertex d.radical, color d.radical w = false →
          X d.radical w = U d.radical w ⊔
            (X d.radical w ⊓ centralizer (stabilizer d.radical w : Set (FreeAmalgam d.radical)))) ∧
        X d.radical z ⊓ Q d.radical r.start = (Z d.radical z ⊓ Q d.radical r.start) ⊔
          (X d.radical z ⊓ centralizer (stabilizer d.radical z : Set (FreeAmalgam d.radical))) ∧
        ∀ Y : Subgroup (FreeAmalgam d.radical), Y ≤ Q d.radical v →
          ⁅Y,X d.radical z ⊓ Q d.radical r.start⁆ = ⁅Y,Z d.radical z ⊓ Q d.radical r.start⁆ ∧
          ⁅Y,X d.radical z ⊓ Q d.radical r.start⁆ = ⁅Y,U d.radical z ⊓ Q d.radical r.start⁆)) := by
  obtain ⟨q,hqe,hqT,hqgen⟩ := SylowShiftChain.original_radical_backward_shift_knownSimple
    hb hcard p hfirst
  obtain ⟨r,hre⟩ := SylowShiftChain.backwardShift_with_edge hb hcard q.path
  obtain ⟨t,hte⟩ := SylowShiftChain.backwardShift_with_edge hb hcard r.path
  have hc := three_shift_kernel_control_knownSimple hb hcard p q r t
  refine ⟨q,r,t,hqe,hqT,hqgen,hre,hte,hc.1,hc.2.1,hc.2.2.1,hc.2.2.2.1,?_⟩
  by_cases hnZ : Z d.radical (q.path.walk.getVert (q.path.walk.length-2)) ≤ normalizer
      (((Z d.radical t.start ⊓ Q d.radical (r.path.walk.getVert (r.path.walk.length-2))) ⊔
        Z d.radical r.start : Subgroup (FreeAmalgam d.radical)) : Set (FreeAmalgam d.radical))
  · exact Or.inl ⟨hnZ,hc.2.2.2.2.1 hnZ⟩
  · have hk := hc.2.2.2.2.2 hnZ
    have hx := three_shift_nonnormalized_full_kernel_knownSimple
      (e := e) (hz := hz) (hn := hn) hb p q r t hnZ
    exact Or.inr ⟨hnZ,hk.1,hk.2.1,hk.2.2,hx⟩

end AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.SylowTerminalKernel
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
