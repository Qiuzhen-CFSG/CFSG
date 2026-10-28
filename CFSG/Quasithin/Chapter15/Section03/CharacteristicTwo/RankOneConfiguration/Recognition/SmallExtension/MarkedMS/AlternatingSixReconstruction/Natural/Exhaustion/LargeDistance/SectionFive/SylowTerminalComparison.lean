module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.SylowTerminalFixed
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.SylowTrappedExclusion

/-!
# Unequal terminal movers and the reverse shifted seed

Mutual whole-core containment forces full omega to fail central generation
at every component vertex if the two terminal movers differ. The full-omega
extension calculation then normalizes the actual reverse restricted kernel
joined with its starting seed. The restriction is by the intermediate whole
core, with every reversed-walk coordinate and transporter retained.

The full backward seed-span is not normalized by the preceding critical
endpoint: otherwise its small normal radius section would lie in the
Baumann slice, contrary to the transported strict slice bound. Consequently
the two whole seeds have nontrivial commutator. The original-radical consumer
supplies these facts, terminal fixed-core escape and both core-product index
bounds on one literal shift chain. Both covers and all central attachments
are retained. The two-conjugate comparison, mover equality and terminal
distance contradiction remain separate mathematical steps.

The internal import reuses the neighboring-seed radius lemma in this source
proof family. Source: Meierfrankenfeld--Stellmacher, Pushing up weak BN-pairs
of rank two (1993), (3.3)(ii), (5.9)--(5.10), printed pp.866--867 and 921--923.
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


variable (s : FullSymmetricAction h e hz hn d)

omit [Finite G] in
private theorem central_generation_transfer
    {a c : Vertex d.radical} (ha : color d.radical a = false)
    (hc : color d.radical c = false)
    (hs : X d.radical a = U d.radical a ⊔
      (X d.radical a ⊓ centralizer (stabilizer d.radical a : Set (FreeAmalgam d.radical)))) :
    X d.radical c = U d.radical c ⊔
      (X d.radical c ⊓ centralizer (stabilizer d.radical c : Set (FreeAmalgam d.radical))) := by
  obtain ⟨g,rfl⟩ := exists_mVertex_of_color d.radical ha
  obtain ⟨k,rfl⟩ := exists_mVertex_of_color d.radical hc
  let f := (MulAut.conj (g⁻¹*k)⁻¹).toMonoidHom
  have hh := congrArg (Subgroup.map f) hs
  rw [Subgroup.map_sup,←map_inf_centralizer_of_injective _ (MulAut.conj _).injective] at hh
  change (X d.radical (mVertex d.radical g)).map (MulAut.conj (g⁻¹*k)⁻¹).toMonoidHom = _ at hh
  rw [←X_act,←U_act,←stabilizer_act] at hh
  simpa only [act_mVertex,mul_inv_cancel_left] using hh

include e hz hn in
/-- Unequal terminal movers force failure of central generation of full
omega at every component vertex, using the established whole-core containment. -/
theorem four_shift_unequal_omega_not_centrally_generated_knownSimple
    (hb : 4 < replacementDistance h d)
    (hcard : Nat.card (d.radical.map (SourceReduction.projection h e hz hn d)) = 16)
    {a a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a a')
    (q : BackwardShift (h := h) p) (r : BackwardShift (h := h) q.path)
    (t : BackwardShift (h := h) r.path) (v : BackwardShift (h := h) t.path)
    (hr : SylowTerminalPath.OrbitPrefix (h := h) r.path (replacementDistance h d))
    (hv : act d.radical v.transporter (t.path.walk.getVert 1) = v.edge)
    (hne : SmallMover.join (U d.radical v.start) (Q d.radical v.start) (Q d.radical v.edge) 4 ≠
      SmallMover.join (U d.radical t.start) (Q d.radical t.start) (Q d.radical v.edge) 4)
    (c : Vertex d.radical) (hc : color d.radical c = false) :
    X d.radical c ≠ U d.radical c ⊔
      (X d.radical c ⊓ centralizer (stabilizer d.radical c : Set (FreeAmalgam d.radical))) := by
  have hcore := (four_shift_core_product_knownSimple hb hcard p q r t v hr hv).1
  have hn := sixteen_unequal_containing_core_not_centrally_generated_knownSimple
    (e := e) (hz := hz) (hn := hn) hb hcard t.path.start_color
    v.adjacent_start v.adjacent_shift hne hcore
  intro hsplit
  exact hn (central_generation_transfer hc t.path.start_color hsplit)

include s in
/-- In the omega extension case, the full opposite omega layer normalizes
any backward critical kernel joined with the starting seed. The kernel is
cut by the second predecessor core, as on printed p.923. -/
theorem backward_full_omega_normalization_of_not_centrally_generated
    (hc : DistanceTwo.CentralLayer d) (hb : 2 < replacementDistance h d)
    {a z : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a z)
    (hsmall : (Q d.radical z).relIndex (Z d.radical a) < 4)
    (q : BackwardShift (h := h) p)
    (hgen : X d.radical z ≠ U d.radical z ⊔
      (X d.radical z ⊓ centralizer (stabilizer d.radical z : Set (FreeAmalgam d.radical)))) :
    X d.radical z ≤ normalizer
      (((Z d.radical q.start ⊓ Q d.radical (p.walk.getVert (p.walk.length-2))) ⊔
        Z d.radical a : Subgroup (FreeAmalgam d.radical)) : Set (FreeAmalgam d.radical)) := by
  let c := p.walk.getVert (p.walk.length-2)
  let K := Z d.radical q.start ⊓ Q d.radical c
  have ht : color d.radical q.edge = true := by
    have hh := adjacent_color_ne d.radical q.adjacent_start
    rw [p.start_color] at hh
    cases he : color d.radical q.edge <;> simp_all
  have hcz : (cosetGraph d.radical).dist c z = 2 := by
    rw [p.dist_end]
    have hl : p.walk.length = replacementDistance h d := p.length_eq_b
    omega
  have hQcG : Q d.radical c ≤ stabilizer d.radical z :=
    Q_le_stabilizer_of_dist_two d.radical c z q.path.end_color hcz
  have hKQ : K ≤ Q d.radical a :=
    (inf_le_left.trans (neighbor_seed_le_radius q.adjacent_start q.adjacent_shift)).trans
      ((replacementGeometry h d).V_le_Q hb a p.start_color)
  have hXq : X d.radical z ⊓ Q d.radical a ≤ stabilizer d.radical q.start :=
    (inf_le_right.trans (Q_le_adjacent_h d.radical ht q.adjacent_start)).trans
      (fun _ hx => hx.2 _ (adjacent_symm d.radical q.adjacent_shift))
  have hXc : X d.radical z ⊓ Q d.radical a ≤ stabilizer d.radical c :=
    (inf_le_left.trans (omegaCenter_le (Q d.radical z))).trans
      (Q_le_stabilizer_of_dist_two d.radical z c p.end_color
        (SimpleGraph.dist_comm.trans hcz))
  have hNK : X d.radical z ⊓ Q d.radical a ≤ normalizer (K : Set (FreeAmalgam d.radical)) :=
    (le_inf (hXq.trans (Z_normalized d.radical q.start))
      (hXc.trans (Q_normalized d.radical c))).trans inf_normalizer_le_normalizer_inf
  rcases critical_X_generation_or_normalization s hc p hsmall K
    (inf_le_right.trans hQcG) hKQ hNK with hs | hn
  · exact (hgen hs).elim
  · exact hn

include e hz hn in
/-- The full backward seed-span cannot be normalized by the preceding
critical endpoint. In particular their whole-seed commutator is nontrivial.
The strict forward-slice bound is transported by the chosen backward actor. -/
theorem backward_seed_span_not_normalized_knownSimple
    (hb : 4 < replacementDistance h d)
    (hcard : Nat.card (d.radical.map (SourceReduction.projection h e hz hn d)) = 16)
    {a z : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a z)
    (hsmall : (Q d.radical z).relIndex (Z d.radical a) < 4)
    (q : BackwardShift (h := h) p) :
    (¬ Z d.radical z ≤ normalizer
      ((Z d.radical q.start ⊔ Z d.radical a : Subgroup (FreeAmalgam d.radical)) :
        Set (FreeAmalgam d.radical))) ∧
      ⁅Z d.radical q.start,Z d.radical z⁆ ≠ ⊥ := by
  have hb2 : 2 < replacementDistance h d := by omega
  let s := fullSymmetricAction_knownSimple h e hz hn d hb2
  have hstrict : 2 < (B d.radical a ((replacementGeometry h d).Z_normal _)).relIndex
      (U d.radical q.start) := by
    have hh := SylowForwardSpan.sixteen_small_forward_slice_strict_at_knownSimple
      (e := e) (hz := hz) (hn := hn) hb hcard p hsmall
    have hm : (B d.radical a ((replacementGeometry h d).Z_normal _)).map
        (MulAut.conj q.transporter⁻¹).toMonoidHom =
          B d.radical a ((replacementGeometry h d).Z_normal _) :=
      mem_normalizer_iff_map_conj_eq.mp (Escape.Propagation.Rigidity.B_normalized
        (geometry := replacementGeometry h d) hb2 a p.start_color
        ((stabilizer d.radical a).inv_mem q.transporter_mem))
    rw [←q.start_eq,U_act,←hm,relIndex_map_map_of_injective _ _ (MulAut.conj _).injective]
    exact hh
  have hnot : ¬ Z d.radical z ≤ normalizer
      ((Z d.radical q.start ⊔ Z d.radical a : Subgroup (FreeAmalgam d.radical)) :
        Set (FreeAmalgam d.radical)) := by
    intro hnorm
    let Y := Z d.radical q.start ⊔ Z d.radical a
    have hYN : stabilizer d.radical a ≤ normalizer (Y : Set (FreeAmalgam d.radical)) := by
      rw [←q.generation]
      apply sup_le _ hnorm
      apply le_trans (le_inf _ _) (normalizer_inf_normalizer_le_normalizer_sup _ _)
      · exact (show Q d.radical q.edge ≤ stabilizer d.radical q.start from
          fun _ hx => hx.2 _ (adjacent_symm d.radical q.adjacent_shift)).trans
            (Z_normalized d.radical q.start)
      · exact (show Q d.radical q.edge ≤ stabilizer d.radical a from
          fun _ hx => hx.2 _ (adjacent_symm d.radical q.adjacent_start)).trans
            (Z_normalized d.radical a)
    have hYV : Y ≤ V d.radical a :=
      sup_le (neighbor_seed_le_radius q.adjacent_start q.adjacent_shift) (Z_le_VBall d.radical a 2)
    have hYB := residual_small_radius_le_slice_knownSimple (e := e)
      hb2 p.start_color Y hYV ((Ltilde_le_stabilizer a).trans hYN)
      (SylowSpanSelection.adjacent_seed_span_index_le_eight
        (e := e) (hz := hz) (hn := hn) hb p.start_color q.adjacent_start q.adjacent_shift)
    have hone : (B d.radical a ((replacementGeometry h d).Z_normal _)).relIndex
        (U d.radical q.start) = 1 := relIndex_eq_one.mpr
      ((DistanceEight.U_le_Z d.radical q.start).trans (le_sup_left.trans hYB))
    omega
  refine ⟨hnot,?_⟩
  intro hzero
  apply hnot
  apply le_trans (le_inf _ _) (normalizer_inf_normalizer_le_normalizer_sup _ _)
  · exact (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hzero)).trans
      (Subgroup.centralizer_le_normalizer _)
  · exact (critical_Z_le_stabilizer d.radical (replacementGeometry h d) a p.start_color
      (by rw [(replacementGeometry h d).distance_constant _ p.start_color]
          exact replacementDistance_pos h d) p.critical).trans (Z_normalized d.radical a)

include e hz hn in
/-- The unequal-mover branch supplies an actual reverse backward shift.
Its full restricted seed is normalized by the opposite whole omega layer;
the restriction is by the intermediate whole core. -/
theorem four_shift_unequal_reverse_normalization_knownSimple
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
    let z := t.path.walk.getVert (t.path.walk.length-2)
    ∃ p' : CriticalPath d.radical (replacementGeometry h d) z v.start,
      (∀ i, p'.walk.getVert i = v.path.walk.getVert (v.path.walk.length-i)) ∧
      ∃ b : BackwardShift (h := h) p',
        act d.radical b.transporter (p'.walk.getVert 1) = b.edge ∧
        ⁅Z d.radical b.start,Z d.radical v.start⁆ ≠ ⊥ ∧
        X d.radical v.start ≤ normalizer
          (((Z d.radical b.start ⊓ Q d.radical t.start) ⊔ Z d.radical z :
            Subgroup (FreeAmalgam d.radical)) : Set (FreeAmalgam d.radical)) := by
  have hb2 : 2 < replacementDistance h d := by omega
  let s := fullSymmetricAction_knownSimple h e hz hn d hb2
  have hc := DistanceTwo.centralLayer_knownSimple G L R h e hz hn d
  let z := t.path.walk.getVert (t.path.walk.length-2)
  let p' : CriticalPath d.radical (replacementGeometry h d) z v.start :=
    ⟨v.path.end_color,v.path.walk.reverse,
      by rw [SimpleGraph.Walk.length_reverse,v.path.shortest,SimpleGraph.dist_comm],
      critical_reverse_pair s hc v.path⟩
  have hsmall₀ := SylowShiftChain.two_backward_shifts_small_moving_knownSimple
    (e := e) (hz := hz) (hn := hn) hb r.path t v
  have hs₀ : (Q d.radical z).relIndex (Z d.radical v.start) < 4 := by
    rw [hsmall₀.2.1]; decide
  have hs : (Q d.radical v.start).relIndex (Z d.radical z) < 4 := by
    rw [(small_critical_indices s hc v.path hs₀).2]; decide
  obtain ⟨b,hbact⟩ := SylowShiftChain.backwardShift_with_edge hb hcard p'
  refine ⟨p',?_,b,hbact,(backward_seed_span_not_normalized_knownSimple hb hcard p' hs b).2,?_⟩
  · intro i
    exact SimpleGraph.Walk.getVert_reverse _ _
  · have hgen := four_shift_unequal_omega_not_centrally_generated_knownSimple
      hb hcard p q r t v hr hv hne v.start v.path.start_color
    have hnorm := backward_full_omega_normalization_of_not_centrally_generated s hc hb2 p' hs b hgen
    have hpred : p'.walk.getVert (p'.walk.length-2) = t.start := by
      change v.path.walk.reverse.getVert (v.path.walk.reverse.length-2) = t.start
      rw [SimpleGraph.Walk.length_reverse,SimpleGraph.Walk.getVert_reverse]
      have hl : v.path.walk.length = replacementDistance h d := v.path.length_eq_b
      rw [show v.path.walk.length-(v.path.walk.length-2)=2 by omega]
      simpa only [Nat.zero_add,SimpleGraph.Walk.getVert_zero] using v.overlap 0 (Nat.zero_le _)
    rwa [hpred] at hnorm

include e hz hn in
/-- Original-radical application of the terminal fixed-core and reverse
normalization comparisons. The original transporter, generating edge and
all path coordinates remain literal. In the unequal-mover branch both
whole-core product bounds and the full-omega extension alternative are
available for the ensuing two-conjugate comparison. -/
theorem original_radical_terminal_fixed_comparison_knownSimple
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
      let z := t.path.walk.getVert (t.path.walk.length-2)
      let D := ⁅Z d.radical v.start,Z d.radical z⁆
      Nat.card D = 2 ∧ D ≤ X d.radical t.start ∧
      (¬ D ≤ fixedCore d.radical t.start) ∧
      (E ≠ J →
        ((Q d.radical t.start).relIndex (Q d.radical t.start ⊔ Q d.radical v.start) ≤ 4 ∧
          (Q d.radical v.start).relIndex (Q d.radical t.start ⊔ Q d.radical v.start) ≤ 4) ∧
        (∀ w, color d.radical w = false → X d.radical w ≠ U d.radical w ⊔
          (X d.radical w ⊓ centralizer (stabilizer d.radical w : Set (FreeAmalgam d.radical)))) ∧
        ∃ p' : CriticalPath d.radical (replacementGeometry h d) z v.start,
          (∀ i, p'.walk.getVert i = v.path.walk.getVert (v.path.walk.length-i)) ∧
          ∃ b : BackwardShift (h := h) p',
            act d.radical b.transporter (p'.walk.getVert 1) = b.edge ∧
            ⁅Z d.radical b.start,Z d.radical v.start⁆ ≠ ⊥ ∧
            X d.radical v.start ≤ normalizer
              (((Z d.radical b.start ⊓ Q d.radical t.start) ⊔ Z d.radical z :
                Subgroup (FreeAmalgam d.radical)) : Set (FreeAmalgam d.radical))) := by
  obtain ⟨q₀,hqe,hqT,hqgen,c,c',p₀,hchain,q,r,t,v,hr,hv,
      _hQtE,_hQvJ,_hprod,hDcard,hDX,_hDcentral,hindices⟩ :=
    original_radical_terminal_core_product_knownSimple hb hcard p hfirst
  have ht : SylowTerminalPath.OrbitPrefix (h := h) t.path (replacementDistance h d) := by
    intro i hi hl
    exact SylowTerminalPath.orbitPrefix_backwardShift hb r.path t hr i (Nat.lt_succ_of_lt hi) hl
  have hnot := orbit_terminal_line_not_le_fixedCore_knownSimple hb hcard q.path r t v ht
  refine ⟨q₀,hqe,hqT,hqgen,c,c',p₀,hchain,q,r,t,v,hr,hv,hDcard,hDX,hnot,?_⟩
  intro hne
  exact ⟨hindices hne,
    four_shift_unequal_omega_not_centrally_generated_knownSimple hb hcard p₀ q r t v hr hv hne,
    four_shift_unequal_reverse_normalization_knownSimple hb hcard p₀ q r t v hr hv hne⟩

end AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
