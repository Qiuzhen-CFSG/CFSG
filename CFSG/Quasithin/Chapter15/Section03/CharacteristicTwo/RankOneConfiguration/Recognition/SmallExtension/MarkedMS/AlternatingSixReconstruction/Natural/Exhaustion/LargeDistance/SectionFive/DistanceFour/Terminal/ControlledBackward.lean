module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.LargeImage
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.CubePaths
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.SylowActor
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.SylowActor

/-!
# Compatible controlled backward paths at distance four

A large critical image supplies a controlled endpoint subgroup and a generating
relative edge normalizer. The Sylow and nonsylow constructions are combined on
the literal natural characteristic replacement. An eligible midpoint is moved
to that edge and then shifted backward through the edge holomorph. The result
retains the controlled subgroup, both geometric transporters, agreement on the
whole edge kernel, all overlapping vertices, and the exact Baumann slice index.

For this same path, the controlled subgroup normalizes the full backward seed
kernel joined with the starting seed, and centralizes the full critical
commutator. If the backward critical image is small, that joined kernel cannot
also be normalized by the relative edge normalizer: generation and the
section-fixed action lemma would put the whole kernel in the Baumann slice,
forcing its moving-cover index to be at most two. The internally constructed
slice has index greater than two.

This is a path-compatibility and kernel obstruction for the large-image branch;
it does not assert the terminal contradiction of (5.12). The source normality
argument, the large-image exclusion and the chosen full-seed slice estimate
still have to be proved in the terminal assembly.

The `import all` of `SylowActor` deliberately reuses its package-internal
relative selector, retaining its actor instead of changing the existing public
boundary. No exceptional graph is used.

Source: Meierfrankenfeld--Stellmacher, *Pushing up weak BN-pairs of rank two*
(1993), (5.2)(i), (5.8), (5.12)(1)--(3), printed pp.913--914,919--920,924--927,
and the relative edge holomorph construction of Section 7.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped commutatorElement Pointwise
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
open CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.Terminal
universe u
variable {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
  {h : SmallMSPair KnownSimple.IsKnownSimple L R} {e : CentralMarking L}
  {hz : center (L ⧸ pCore 2 L) = ⊥} {hn : InitialNatural h e hz}
  {d : Replacement L R}

include e hz hn in
private theorem controlled_neighbor
    (hb : 2 < replacementDistance h d)
    {a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) a')
    (hlarge : 4 ≤ (Q d.radical a').relIndex (Z d.radical (alpha d.radical))) :
    ∃ W : Subgroup (FreeAmalgam d.radical), W ≤ U d.radical a' ∧
      ⁅V d.radical (alpha d.radical) ⊓ Q d.radical (p.walk.getVert (p.walk.length-2)), W⁆ ≤
        Z d.radical (alpha d.radical) ∧
      (¬ W ≤ Q d.radical (alpha d.radical)) ∧
      ∃ t, Adjacent d.radical (alpha d.radical) t ∧
        (normalizer (Q d.radical t : Set (FreeAmalgam d.radical)) ⊓
          stabilizer d.radical (alpha d.radical)) ⊔ W = stabilizer d.radical (alpha d.radical) := by
  classical
  by_cases hs : ∃ P : Sylow 2 (L ⊔ R : Subgroup G),
      (P : Subgroup (L ⊔ R : Subgroup G)) = R.subgroupOf (L ⊔ R)
  · obtain ⟨P,hP⟩ := hs
    exact SylowActor.large_image_controlled_neighbor_knownSimple
      (e := e) (hz := hz) (hn := hn) hb P hP p hlarge
  · obtain ⟨W,hWU,hbound,hWne,t,hat,hgen⟩ :=
      nonsylow_large_image_controlled_neighbor_knownSimple
        (e := e) (hz := hz) (hn := hn) hb hs p hlarge
    have hQG : Q d.radical t ≤ stabilizer d.radical (alpha d.radical) :=
      fun _ hx => hx.2 _ (adjacent_symm d.radical hat)
    have hWG : W ≤ stabilizer d.radical (alpha d.radical) :=
      le_sup_right.trans_eq hgen
    refine ⟨W,hWU,hbound,hWne,t,hat,le_antisymm (sup_le inf_le_right hWG) ?_⟩
    exact hgen.symm.le.trans
      (sup_le_sup_right (le_inf (Q d.radical t).le_normalizer hQG) W)

include e hz hn in
/-- A large critical image at distance four has a compatible controlled
backward path with a strict slice and a full seed-kernel normalizer obstruction.
All actors and kernels in the conclusion belong to the same chosen path. -/
theorem large_image_controlled_backward_knownSimple
    (hb : replacementDistance h d = 4)
    {a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) a')
    (hlarge : 4 ≤ (Q d.radical a').relIndex (Z d.radical (alpha d.radical))) :
    ∃ W : Subgroup (FreeAmalgam d.radical), W ≤ U d.radical a' ∧
      (¬ W ≤ Q d.radical (alpha d.radical)) ∧
      ⁅V d.radical (alpha d.radical) ⊓ Q d.radical (p.walk.getVert 2), W⁆ ≤
        Z d.radical (alpha d.radical) ∧
      ∃ t c, Adjacent d.radical (alpha d.radical) t ∧ Adjacent d.radical c t ∧
        (normalizer (Q d.radical t : Set (FreeAmalgam d.radical)) ⊓
          stabilizer d.radical (alpha d.radical)) ⊔ W = stabilizer d.radical (alpha d.radical) ∧
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
          ⁅Z d.radical c ⊓ Q d.radical (p.walk.getVert 2), W⁆ ≤ Z d.radical (alpha d.radical) ∧
          W ≤ normalizer (((Z d.radical c ⊓ Q d.radical (p.walk.getVert 2) ⊔
            Z d.radical (alpha d.radical)) : Subgroup (FreeAmalgam d.radical)) : Set (FreeAmalgam d.radical)) ∧
          ⁅Z d.radical c, Z d.radical (p.walk.getVert 2)⁆ ≤
            centralizer (W : Set (FreeAmalgam d.radical)) ∧
          ((Q d.radical (p.walk.getVert 2)).relIndex (Z d.radical c) < 4 →
            ¬ normalizer (Q d.radical t : Set (FreeAmalgam d.radical)) ⊓
                stabilizer d.radical (alpha d.radical) ≤
              normalizer (((Z d.radical c ⊓ Q d.radical (p.walk.getVert 2) ⊔
                Z d.radical (alpha d.radical)) : Subgroup (FreeAmalgam d.radical)) : Set (FreeAmalgam d.radical))) := by
  have hb2 : 2 < replacementDistance h d := by omega
  have hl : p.walk.length = 4 := p.length_eq_b.trans hb
  let s := fullSymmetricAction_knownSimple h e hz hn d hb2
  have hc := DistanceTwo.centralLayer_knownSimple G L R h e hz hn d
  obtain ⟨W,hWU,hbound,hWne,t,hat,hgen⟩ := controlled_neighbor
    (e := e) (hz := hz) (hn := hn) hb2 p hlarge
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
  have hbound' : ⁅V d.radical (alpha d.radical) ⊓ Q d.radical (p.walk.getVert 2), W⁆ ≤
      Z d.radical (alpha d.radical) := by
    simpa only [hl,show 4-2=2 from rfl] using hbound
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
  have hmove : ⁅K,W⁆ ≤ Z d.radical (alpha d.radical) :=
    (commutator_mono (le_inf hKV inf_le_right) le_rfl).trans hbound'
  have hZmove : ⁅Z d.radical (alpha d.radical),W⁆ ≤ Z d.radical (alpha d.radical) :=
    le_normalizer_iff_commutator_le_left.mp (hWG.trans (Z_normalized d.radical _))
  have hDmove : ⁅D,W⁆ ≤ Z d.radical (alpha d.radical) :=
    commutator_sup_le_of_relative_normal (stabilizer d.radical (alpha d.radical))
      K (Z d.radical (alpha d.radical)) W (Z d.radical (alpha d.radical))
      (Z_normalized d.radical _) (hKV.trans ((replacementGeometry h d).V_local _ rfl hb2))
      (Z_le_stabilizer d.radical _) hmove hZmove
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
      (centralizer_le (hWU.trans (DistanceEight.U_le_Z d.radical _)))
  refine ⟨W,hWU,hWne,hbound',t,c,hat,hc't,hgen,q',hq1',hq2',hq3',hidx',hstrict',
    ⟨x,hx,hxt,k,hk,rfl,g,hg,hagree⟩,hmove,hWD,hcent,?_⟩
  intro hsmall hND
  have hDN : stabilizer d.radical (alpha d.radical) ≤ normalizer (D : Set (FreeAmalgam d.radical)) := by
    rw [←hgen]
    exact sup_le hND hWD
  have hDB : D ≤ B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _) :=
    normalized_radius_le_slice_of_actor_at s hb2 rfl D W
      (sup_le hKV (Z_le_VBall d.radical _ 2)) hDN hWG hWne hDmove
  have hKB : K ≤ B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _) :=
    le_sup_left.trans hDB
  let := finite_Z d.radical c
  have hidxK := relIndex_le_of_le_left hKB
    (index_ne_zero_of_finite (H := K.subgroupOf (Z d.radical c)))
  change (B d.radical (alpha d.radical) _).relIndex (Z d.radical c) ≤
    (Z d.radical c ⊓ Q d.radical (p.walk.getVert 2)).relIndex (Z d.radical c) at hidxK
  rw [inf_relIndex_left] at hidxK
  have hsmallidx := (small_critical_indices s hc q' hsmall).1
  have hle : (B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _)).relIndex
      (U d.radical c) ≤ 2 :=
    ((relIndex_le_of_le_right (DistanceEight.U_le_Z d.radical c)
      index_ne_zero_of_finite).trans hidxK).trans_eq hsmallidx
  exact (not_le_of_gt hstrict') hle

end AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.Terminal
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
