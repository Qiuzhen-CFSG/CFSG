module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.Terminal.MixedGeneration
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.Terminal.EightBackward
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.Terminal.FullSeedBackward
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.Terminal.EightBackward
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.SylowActor

/-!
# Large backward selection for all radical images

A large critical path admits a controlled full endpoint restriction which
generates the starting stabilizer with an actual edge kernel. The radical
image has order four, eight or sixteen. MixedGeneration supplies the
order-four branch, EightBackward supplies order eight, and the proved
relative-normalizer identity supplies order sixteen.

Apply the relative holomorph with this same seed and edge. Its backward
path retains both transporters, all overlapping vertices, the original
Baumann slice index, the full kernel joined with the initial seed and the
exact critical commutator. The selected actor normalizes that join and
fixes the backward critical commutator. FullCoverMovement excludes a small
backward image, so the backward critical image is large in every branch.

This completes the small-backward exclusion used in the large-image branch
of MS93 (5.12)(2). The large-image contradiction, the chosen large-slice
bound and the selected terminal theorem still require proof. No bound on
the whole residual-core product is inferred from the movement estimates.

Source: Meierfrankenfeld–Stellmacher, *Pushing up weak BN-pairs of rank two*
(1993), (5.2)(i), (5.12)(1)–(2), printed pp.913–914,924–926, and the
relative edge holomorph in Section 7, pp.932–933. The internal imports reuse
the existing prescribed-seed selectors without changing their boundaries.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Theory.SpecificGroups.SymmetricSix
open CFSG.Quasithin.ChapterB.Offenders CFSG.Quasithin.ChapterB.Offenders.Six
open Theory.SpecificGroups.SymmetricSix.BinaryFlags
open scoped commutatorElement Pointwise IsMulCommutative
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.Terminal
local notation "S" => Equiv.Perm (Fin 6)
universe u
variable {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
  {h : SmallMSPair KnownSimple.IsKnownSimple L R} {e : CentralMarking L}
  {hz : center (L ⧸ pCore 2 L) = ⊥} {hn : InitialNatural h e hz}
  {d : Replacement L R} (s : FullSymmetricAction h e hz hn d)

include s in
/-- For every radical image and both covers, a large critical path has a
controlled full endpoint restriction generating with an actual edge kernel. -/
theorem large_image_full_seed_generating_neighbor
    (hc : DistanceTwo.CentralLayer d) (hb : replacementDistance h d = 4)
    {z : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) z)
    (hlarge : 4 ≤ (Q d.radical z).relIndex (Z d.radical (alpha d.radical))) :
    ∃ E : Subgroup (FreeAmalgam d.radical),
      Z d.radical (p.walk.getVert 3) ≤ E ∧ E ≤ Z d.radical z ∧
      E.relIndex (Z d.radical z) ≤ 2 ∧
      ⁅Z d.radical (alpha d.radical),E⁆ =
        ⁅Z d.radical (alpha d.radical),Z d.radical z⁆ ∧
      ⁅V d.radical (alpha d.radical) ⊓ Q d.radical (p.walk.getVert 2),E⁆ =
        ⁅Z d.radical (alpha d.radical),Z d.radical z⁆ ∧
      (¬ E ≤ Q d.radical (alpha d.radical)) ∧
      ∃ t, Adjacent d.radical (alpha d.radical) t ∧
        (normalizer (Q d.radical t : Set (FreeAmalgam d.radical)) ⊓
          stabilizer d.radical (alpha d.radical)) ⊔ E = stabilizer d.radical (alpha d.radical) ∧
        Q d.radical t ⊔ E = stabilizer d.radical (alpha d.radical) := by
  have hb2 : 2 < replacementDistance h d := by omega
  let A := d.radical.map s.projection
  by_cases hfour : Nat.card A = 4
  · exact four_full_seed_generating_neighbor s hc hb hfour p hlarge
  by_cases height : Nat.card A = 8
  · exact eight_full_seed_generating_neighbor s hc hb height p hlarge
  have hlow : 4 ≤ Nat.card A := by
    have hh := large_distance_radical_image_four_le_knownSimple
      (e := e) (hz := hz) (hn := hn) hb2
    rwa [←SourceReduction.fullSymmetricAction_projection_unique h e hz hn d s] at hh
  have hp : IsPGroup 2 A := (replacement_radical_isPGroup h d).map s.projection
  obtain ⟨P,hAP⟩ := hp.exists_le_sylow
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq S P sylow
  have hPcard : Nat.card (P : Subgroup S) = 16 := by
    have hh := congrArg (fun P : Sylow 2 S => Nat.card (P : Subgroup S)) hg
    change Nat.card ((P : Subgroup S).map (MulAut.conj g).toMonoidHom) = Nat.card sylowCarrier at hh
    rwa [card_map_of_injective (MulAut.conj g).injective,card_sylowCarrier] at hh
  have hu : Nat.card A ≤ 16 := (card_le_of_le hAP).trans_eq hPcard
  have hsixteen : Nat.card A = 16 := by
    obtain ⟨n,hn⟩ := hp.exists_card_eq
    have hn4 : n ≤ 4 := by
      apply (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp
      simpa only [hn] using hu
    have hvals : Nat.card A = 1 ∨ Nat.card A = 2 ∨ Nat.card A = 4 ∨
        Nat.card A = 8 ∨ Nat.card A = 16 := by
      rw [hn]
      interval_cases n <;> norm_num
    omega
  obtain ⟨E,hFE,hEZ,hi,hcomm,hcontrol,hEn,t,hat,hgen,_⟩ :=
    full_seed_generating_neighbor s hc hb p hlarge
  refine ⟨E,hFE,hEZ,hi,hcomm,hcontrol,hEn,t,hat,hgen,?_⟩
  have hh := SylowLarge.sixteen_edge_relative_normalizer_knownSimple
    (e := e) (hz := hz) (hn := hn) hb2 (by
      rwa [←SourceReduction.fullSymmetricAction_projection_unique h e hz hn d s]) rfl hat
  rwa [hh] at hgen

include e hz hn in
/-- The same full-seed selection has a large backward critical image for
every radical image, with its generating kernel, relative
normalizer, central attachment and literal transporters retained. -/
theorem full_seed_backward_large_knownSimple
    (hb : replacementDistance h d = 4)
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
    large_image_full_seed_generating_neighbor s hc hb p hlarge
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
