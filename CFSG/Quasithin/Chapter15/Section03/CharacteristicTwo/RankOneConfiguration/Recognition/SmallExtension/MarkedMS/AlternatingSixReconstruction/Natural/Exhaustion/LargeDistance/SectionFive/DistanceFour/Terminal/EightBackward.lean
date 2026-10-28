module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.Terminal.EightGeneration
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.SylowActor

/-!
# Full-seed backward selection for every image of order eight

Choose the full endpoint restriction with its attachment, index at most two,
exact critical commutator and marked even involution. EightGeneration chooses
an incident edge whose kernel generates with this same restriction. The
relative holomorph selection preserves the full seed, the literal relative
normalizer, both transporters, every overlapping vertex and the strict
Baumann slice index.

A small backward image would contradict FullCoverMovement.strict_small_actor_false:
the same actor controls the full backward-kernel join and fixes its critical
commutator, and edge-kernel generation is now proved. Thus the backward image
is large for every image of order eight, including original-Sylow replacements,
with both moving covers and the complete central attachments retained.

This removes the small-backward alternative in this radical-image branch.
The large-image contradiction, chosen large-slice bound and source application
remain separate obligations; no whole residual-core upper bound is asserted.

Source: Meierfrankenfeld–Stellmacher, *Pushing up weak BN-pairs of rank two*
(1993), (5.2)(i) and (5.12)(1)–(2), printed pp.913–914,924–926,
and the relative edge holomorph of Section 7, pp.932–933.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped commutatorElement Pointwise IsMulCommutative
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.Terminal
universe u
variable {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
  {h : SmallMSPair KnownSimple.IsKnownSimple L R} {e : CentralMarking L}
  {hz : center (L ⧸ pCore 2 L) = ⊥} {hn : InitialNatural h e hz}
  {d : Replacement L R} (s : FullSymmetricAction h e hz hn d)

include s in
private theorem eight_full_seed_generating_neighbor
    (hc : DistanceTwo.CentralLayer d) (hb : replacementDistance h d = 4)
    (hcard : Nat.card (d.radical.map s.projection) = 8)
    {a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) a')
    (hlarge : 4 ≤ (Q d.radical a').relIndex (Z d.radical (alpha d.radical))) :
    ∃ E : Subgroup (FreeAmalgam d.radical),
      Z d.radical (p.walk.getVert 3) ≤ E ∧ E ≤ Z d.radical a' ∧
      E.relIndex (Z d.radical a') ≤ 2 ∧
      ⁅Z d.radical (alpha d.radical),E⁆ =
        ⁅Z d.radical (alpha d.radical),Z d.radical a'⁆ ∧
      ⁅V d.radical (alpha d.radical) ⊓ Q d.radical (p.walk.getVert 2),E⁆ =
        ⁅Z d.radical (alpha d.radical),Z d.radical a'⁆ ∧
      (¬ E ≤ Q d.radical (alpha d.radical)) ∧
      ∃ t, Adjacent d.radical (alpha d.radical) t ∧
        (normalizer (Q d.radical t : Set (FreeAmalgam d.radical)) ⊓
          stabilizer d.radical (alpha d.radical)) ⊔ E = stabilizer d.radical (alpha d.radical) ∧
        Q d.radical t ⊔ E = stabilizer d.radical (alpha d.radical) := by
  have hb2 : 2 < replacementDistance h d := by omega
  obtain ⟨E,hFE,hEZ,hi,hcomm,hcontrol,a,ha,hao,haeven⟩ :=
    large_image_full_seed_even_control s hc hb p hlarge
  have hEG : E ≤ stabilizer d.radical (alpha d.radical) := hEZ.trans
    (critical_Z_le_stabilizer d.radical (replacementGeometry h d) _ rfl
      (replacementDistance_pos h d) p.critical)
  have hEn : ¬ E ≤ Q d.radical (alpha d.radical) := by
    intro hEQ
    have hker : E.comap (embedM d.radical) ≤ s.projection.ker := by
      rw [s.projection_kernel]
      have hh := comap_mono (f := embedM d.radical) hEQ
      rwa [Q_alpha_comap d.radical (replacement_radical_isPGroup h d)
        (replacement_core_le_radical h d)] at hh
    have he := (Subgroup.map_eq_bot_iff (E.comap (embedM d.radical))).mpr hker
    have ha1 : a = 1 := mem_bot.mp (he ▸ ha)
    rw [ha1,orderOf_one] at hao
    omega
  obtain ⟨t,hat,hgen⟩ := eight_generating_neighbor_of_even_actor s hcard E hEG a ha hao haeven
  have hQG : Q d.radical t ≤ stabilizer d.radical (alpha d.radical) :=
    fun _ hx => hx.2 _ (adjacent_symm d.radical hat)
  refine ⟨E,hFE,hEZ,hi,hcomm,hcontrol,hEn,t,hat,?_,hgen⟩
  apply le_antisymm (sup_le inf_le_right hEG)
  exact hgen.symm.le.trans
    (sup_le_sup_right (le_inf (Q d.radical t).le_normalizer hQG) E)

include e hz hn in
/-- The same full-seed selection has a large backward critical image for
every radical image of order eight, with its generating kernel, relative
normalizer, central attachment and literal transporters retained. -/
theorem eight_full_seed_backward_large_knownSimple
    (hb : replacementDistance h d = 4)
    (himage : Nat.card (d.radical.map (SourceReduction.projection h e hz hn d)) = 8)
    {a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) a')
    (hlarge : 4 ≤ (Q d.radical a').relIndex (Z d.radical (alpha d.radical))) :
    ∃ W : Subgroup (FreeAmalgam d.radical),
      Z d.radical (p.walk.getVert 3) ≤ W ∧ W ≤ Z d.radical a' ∧
      W.relIndex (Z d.radical a') ≤ 2 ∧
      ⁅Z d.radical (alpha d.radical),W⁆ =
        ⁅Z d.radical (alpha d.radical),Z d.radical a'⁆ ∧
      (¬ W ≤ Q d.radical (alpha d.radical)) ∧
      ⁅V d.radical (alpha d.radical) ⊓ Q d.radical (p.walk.getVert 2), W⁆ =
        ⁅Z d.radical (alpha d.radical),Z d.radical a'⁆ ∧
      ∃ t c, Adjacent d.radical (alpha d.radical) t ∧ Adjacent d.radical c t ∧
        (normalizer (Q d.radical t : Set (FreeAmalgam d.radical)) ⊓
          stabilizer d.radical (alpha d.radical)) ⊔ W = stabilizer d.radical (alpha d.radical) ∧
        Q d.radical t ⊔ W = stabilizer d.radical (alpha d.radical) ∧
        ∃ q : CriticalPath d.radical (replacementGeometry h d) c (p.walk.getVert 2),
          q.walk.getVert 1 = t ∧ q.walk.getVert 2 = alpha d.radical ∧
          q.walk.getVert 3 = p.walk.getVert 1 ∧
          (B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _)).relIndex
            (U d.radical c) =
          (B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _)).relIndex
            (U d.radical (p.walk.getVert 2)) ∧
          2 < (B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _)).relIndex
            (U d.radical c) ∧
          (∃ x ∈ stabilizer d.radical (alpha d.radical), act d.radical x (p.walk.getVert 1) = t ∧
            ∃ k ∈ stabilizer d.radical t, c = act d.radical k (act d.radical x (p.walk.getVert 2)) ∧
              ∃ g ∈ normalizer (Q d.radical t : Set (FreeAmalgam d.radical)) ⊓
                  stabilizer d.radical (alpha d.radical),
                ∀ v ∈ Q d.radical t, (MulAut.conj k⁻¹) v = (MulAut.conj g) v) ∧
          ⁅Z d.radical c ⊓ Q d.radical (p.walk.getVert 2), W⁆ ≤
            ⁅Z d.radical (alpha d.radical),Z d.radical a'⁆ ∧
          ⁅(Z d.radical c ⊓ Q d.radical (p.walk.getVert 2)) ⊔ Z d.radical (alpha d.radical),W⁆ =
            ⁅Z d.radical (alpha d.radical),Z d.radical a'⁆ ∧
          W ≤ normalizer (((Z d.radical c ⊓ Q d.radical (p.walk.getVert 2) ⊔
            Z d.radical (alpha d.radical)) : Subgroup (FreeAmalgam d.radical)) : Set (FreeAmalgam d.radical)) ∧
          ⁅Z d.radical c, Z d.radical (p.walk.getVert 2)⁆ ≤
            centralizer (W : Set (FreeAmalgam d.radical)) ∧
          4 ≤ (Q d.radical (p.walk.getVert 2)).relIndex (Z d.radical c) := by
  have hb2 : 2 < replacementDistance h d := by omega
  have hl : p.walk.length = 4 := p.length_eq_b.trans hb
  let s := fullSymmetricAction_knownSimple h e hz hn d hb2
  have hc := DistanceTwo.centralLayer_knownSimple G L R h e hz hn d
  obtain ⟨W,hFE,hWZ,hindex,hcritical,hexact,hWne,t,hat,hgen,hgenQ⟩ :=
    eight_full_seed_generating_neighbor s hc hb (by
      rwa [SourceReduction.fullSymmetricAction_projection_unique h e hz hn d s]) p hlarge
  have hRZ : ⁅Z d.radical (alpha d.radical),Z d.radical a'⁆ ≤ Z d.radical (alpha d.radical) :=
    ((critical_Z_commutator_le_moving (h := h) p).trans inf_le_left).trans
      (DistanceEight.U_le_Z d.radical _)
  have hbound' := hexact.le.trans hRZ
  have hbound : ⁅V d.radical (alpha d.radical) ⊓
      Q d.radical (p.walk.getVert (p.walk.length-2)),W⁆ ≤ Z d.radical (alpha d.radical) := by
    simpa only [hl,show 4-2=2 from rfl] using hbound'
  have hWG : W ≤ stabilizer d.radical (alpha d.radical) := le_sup_right.trans_eq hgen
  have ha1 : Adjacent d.radical (alpha d.radical) (p.walk.getVert 1) := by
    apply (cosetGraph_adj d.radical _ _).mp
    simpa only [SimpleGraph.Walk.getVert_zero] using p.walk.adj_getVert_succ (i := 0) (by omega)
  have hd1 : Adjacent d.radical (p.walk.getVert 2) (p.walk.getVert 1) := by
    exact adjacent_symm d.radical ((cosetGraph_adj d.radical _ _).mp
      (p.walk.adj_getVert_succ (i := 1) (by omega)))
  obtain ⟨x,hx,hxt⟩ := stabilizer_transitive_neighbors d.radical (alpha d.radical) ha1 hat
  have hct : Adjacent d.radical (act d.radical x (p.walk.getVert 2)) t := by
    rw [←hxt]
    exact (adjacent_act_iff d.radical x _ _).mpr hd1
  have hB : (B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _)).map
      (MulAut.conj x⁻¹).toMonoidHom = B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _) :=
    mem_normalizer_iff_map_conj_eq.mp (Escape.Propagation.Rigidity.B_normalized
      hb2 (alpha d.radical) rfl ((stabilizer d.radical (alpha d.radical)).inv_mem hx))
  have hi : (B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _)).relIndex
      (U d.radical (act d.radical x (p.walk.getVert 2))) =
      (B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _)).relIndex
        (U d.radical (p.walk.getVert 2)) := by
    rw [U_act,←hB,relIndex_map_map_of_injective _ _ (MulAut.conj x⁻¹).injective,hB]
  have hstrict := large_image_forward_slice_gt_two_knownSimple
    (e := e) (hz := hz) (hn := hn) hb p hlarge
  have hel : ¬ U d.radical (act d.radical x (p.walk.getVert 2)) ≤
      B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _) := by
    intro hh
    have he := relIndex_eq_one.mpr hh
    rw [hi] at he
    omega
  obtain ⟨k,hk,g,hg,hagree,q,hq1,hover,hidx⟩ := SylowActor.relative_controlled_backward_shift
    s hb2 p W hWG hWne hbound hat hct hgen hel
  have hc't : Adjacent d.radical (act d.radical k (act d.radical x (p.walk.getVert 2))) t := by
    have hfix : act d.radical k t = t := hk
    simpa only [hfix] using (adjacent_act_iff d.radical k _ t).mpr hct
  have hq2 : q.walk.getVert 2 = alpha d.radical := by
    simpa only [Nat.zero_add,SimpleGraph.Walk.getVert_zero] using hover 0 (by omega)
  have hq3 : q.walk.getVert 3 = p.walk.getVert 1 := hover 1 (by omega)
  have hidx' := hidx.trans hi
  have hstrict' : 2 < (B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _)).relIndex
      (U d.radical (act d.radical k (act d.radical x (p.walk.getVert 2)))) := by
    rw [hidx']
    exact hstrict
  have hout : ∃ q' : CriticalPath d.radical (replacementGeometry h d)
      (act d.radical k (act d.radical x (p.walk.getVert 2))) (p.walk.getVert 2),
      q'.walk.getVert 1 = t ∧ q'.walk.getVert 2 = alpha d.radical ∧
      q'.walk.getVert 3 = p.walk.getVert 1 := by
    have hex : ∃ q' : CriticalPath d.radical (replacementGeometry h d)
        (act d.radical k (act d.radical x (p.walk.getVert 2))) (p.walk.getVert (p.walk.length-2)),
        q'.walk.getVert 1 = t ∧ q'.walk.getVert 2 = alpha d.radical ∧
        q'.walk.getVert 3 = p.walk.getVert 1 := ⟨q,hq1,hq2,hq3⟩
    have he : p.walk.length-2 = 2 := by omega
    rw [he] at hex
    exact hex
  obtain ⟨q',hq1',hq2',hq3'⟩ := hout
  let c := act d.radical k (act d.radical x (p.walk.getVert 2))
  let K := Z d.radical c ⊓ Q d.radical (p.walk.getVert 2)
  let D := K ⊔ Z d.radical (alpha d.radical)
  have hdist : (cosetGraph d.radical).dist c (alpha d.radical) ≤ 2 := by
    have h1 : (cosetGraph d.radical).dist c t = 1 :=
      SimpleGraph.dist_eq_one_iff_adj.mpr ((cosetGraph_adj d.radical _ _).mpr hc't)
    have h2 : (cosetGraph d.radical).dist t (alpha d.radical) = 1 :=
      SimpleGraph.dist_eq_one_iff_adj.mpr ((cosetGraph_adj d.radical _ _).mpr (adjacent_symm d.radical hat))
    simpa only [h1,h2] using (cosetGraph_connected d.radical).dist_triangle
      (u := c) (v := t) (w := alpha d.radical)
  have hKV : K ≤ V d.radical (alpha d.radical) :=
    inf_le_left.trans ((Z_le_localZSpan d.radical _ _).trans (localZSpan_le_V d.radical hdist))
  have hmove : ⁅K,W⁆ ≤ ⁅Z d.radical (alpha d.radical),Z d.radical a'⁆ :=
    (commutator_mono (le_inf hKV inf_le_right) le_rfl).trans_eq hexact
  have hZaY : Z d.radical (alpha d.radical) ≤
      V d.radical (alpha d.radical) ⊓ Q d.radical (p.walk.getVert 2) := by
    apply le_inf (Z_le_VBall d.radical _ 2)
    apply Z_le_Q_of_dist_lt d.radical _ ((replacementGeometry h d).exists_critical _ rfl)
    rw [(replacementGeometry h d).distance_constant _ rfl,p.dist_start (by omega)]
    exact hb2
  have hDexact : ⁅D,W⁆ = ⁅Z d.radical (alpha d.radical),Z d.radical a'⁆ :=
    le_antisymm ((commutator_mono (sup_le (le_inf hKV inf_le_right) hZaY) le_rfl).trans_eq hexact)
      (hcritical.ge.trans (commutator_mono le_sup_right le_rfl))
  have hDmove : ⁅D,W⁆ ≤ Z d.radical (alpha d.radical) := hDexact.le.trans hRZ
  have hWD : W ≤ normalizer (D : Set (FreeAmalgam d.radical)) :=
    le_normalizer_iff_commutator_le_left.mpr (hDmove.trans le_sup_right)
  have hcent : ⁅Z d.radical c,Z d.radical (p.walk.getVert 2)⁆ ≤
      centralizer (W : Set (FreeAmalgam d.radical)) := by
    have hpre : ⁅Z d.radical c,Z d.radical (p.walk.getVert 2)⁆ ≤ Z d.radical (p.walk.getVert 2) :=
      ((critical_Z_commutator_le_moving (h := h) q').trans inf_le_right).trans
        (DistanceEight.U_le_Z d.radical _)
    have hQ : Z d.radical (p.walk.getVert 2) ≤ Q d.radical a' := by
      apply Z_le_Q_of_dist_lt d.radical _ ((replacementGeometry h d).exists_critical _ q'.end_color)
      rw [(replacementGeometry h d).distance_constant _ q'.end_color,p.dist_end]
      change p.walk.length-2 < replacementDistance h d
      omega
    have hCZ : Q d.radical a' ≤ centralizer (Z d.radical a' : Set (FreeAmalgam d.radical)) :=
      le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp
        (Z_centralizes_Q d.radical a' p.end_color))
    exact (hpre.trans (hQ.trans hCZ)).trans
      (centralizer_le hWZ)
  have hback : 4 ≤ (Q d.radical (p.walk.getVert 2)).relIndex (Z d.radical c) := by
    by_contra! hsmall
    apply strict_small_actor_false s hc hb q' hsmall W
    · simpa only [hq1',hq2'] using hgenQ
    · simpa only [hq2'] using hstrict'
    · simpa only [hq2'] using hWne
    · rw [hq2']
      exact hDmove
    · exact hcent
  exact ⟨W,hFE,hWZ,hindex,hcritical,hWne,hexact,t,c,hat,hc't,hgen,hgenQ,
    q',hq1',hq2',hq3',hidx',hstrict',⟨x,hx,hxt,k,hk,rfl,g,hg,hagree⟩,
    hmove,hDexact,hWD,hcent,hback⟩

end AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.Terminal
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
