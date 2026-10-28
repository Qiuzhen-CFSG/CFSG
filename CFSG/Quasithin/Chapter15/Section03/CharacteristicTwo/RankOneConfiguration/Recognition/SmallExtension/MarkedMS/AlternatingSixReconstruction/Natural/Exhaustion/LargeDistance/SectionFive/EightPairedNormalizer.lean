module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.EightTrappedKernel
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.SylowCompatible
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.SylowNormalizer
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.SylowAdjacent
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.CubePairedKernel

import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.SylowPairedFixer
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.SylowTrappedExclusion
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.SylowSpanSelection

import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.CubeFullKernel

/-!
# Paired relative-normalizer movers in the image-eight branch

For the actual minimum characteristic replacement, the larger mover in the
relative edge normalizer admits a residual transporter pairing two critical
paths. Equal neighboring movers control the whole seed, including its central
attachment. A strict Baumann slice then excludes simultaneous trapping: the
zero second commutator is treated separately, while two nonzero displacement
lines coincide and are fixed by the paired generators.

The original-radical consumer constructs an overlapping backward critical path,
retaining index two over the replacement edge and both moving covers of orders
sixteen and thirty-two. Trapping consequently bounds every equal-mover slice
and identifies the full reverse kernel with its predecessor slice when the
last relative movers agree. Unequal-mover slices and unconditional radius
escape remain separate obligations.

Source: Meierfrankenfeld--Stellmacher, *Pushing up weak BN-pairs of rank two*,
(5.6)--(5.8), printed pp.918--920. This module proves the equal-relative-mover
part of (5.7) on the natural replacement graph, not the full statement of (5.8).
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open CFSG.Quasithin.ChapterB.Offenders CFSG.Quasithin.ChapterB.Offenders.Six
open scoped commutatorElement Pointwise IsMulCommutative
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.EightPairedNormalizer
universe u
variable {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
  {h : SmallMSPair KnownSimple.IsKnownSimple L R} {e : CentralMarking L}
  {hz : center (L ⧸ pCore 2 L) = ⊥} {hn : InitialNatural h e hz}
  {d : Replacement L R}

include e hz hn in
/-- The same residual element pairs the full relative-normalizer movers and
critical endpoints. The actual edge core remains distinct from its normalizer. -/
theorem paired_normalizer_neighbor_knownSimple
    (hb : 4 < replacementDistance h d)
    {a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) a')
    (hsmall : (Q d.radical a').relIndex (Z d.radical (alpha d.radical)) < 4) :
    ∃ t, Adjacent d.radical (alpha d.radical) t ∧
      ∃ x ∈ Ltilde d.radical (alpha d.radical),
        x^3 ∈ Q d.radical (alpha d.radical) ∧
        let N := normalizer (Q d.radical t : Set (FreeAmalgam d.radical)) ⊓
          stabilizer d.radical (alpha d.radical)
        let J := SmallMover.join (U d.radical (alpha d.radical))
          (Q d.radical (alpha d.radical)) N 4
        N ⊔ Z d.radical a' = stabilizer d.radical (alpha d.radical) ∧
        N ⊔ Z d.radical (act d.radical x a') = stabilizer d.radical (alpha d.radical) ∧
        J ⊔ Z d.radical a' ⊔ Z d.radical (act d.radical x a') = stabilizer d.radical (alpha d.radical) ∧
        J ⊔ J.map (MulAut.conj x).toMonoidHom = stabilizer d.radical (alpha d.radical) ∧
        (Z d.radical (alpha d.radical) ⊓ centralizer (J : Set (FreeAmalgam d.radical))) ⊓
          centralizer (J.map (MulAut.conj x).toMonoidHom : Set (FreeAmalgam d.radical)) =
          Z d.radical (alpha d.radical) ⊓
            centralizer (stabilizer d.radical (alpha d.radical) : Set (FreeAmalgam d.radical)) := by
  let s := fullSymmetricAction_knownSimple h e hz hn d (by omega)
  have hc := DistanceTwo.centralLayer_knownSimple G L R h e hz hn d
  obtain ⟨a,ha,hswap⟩ := small_critical_image_swap s hc p hsmall
  obtain ⟨u,hN,_,hj,himage,_⟩ := SylowSmallMovers.normalizer_small_movers_knownSimple
    (e := e) (hz := hz) (hn := hn) hb
  let N₀ := normalizer (d.radical : Set d.overgroup)
  let J₀ := SmallMover.join (replacementMoved d) (pCore 2 d.overgroup) N₀ 4
  have hJimage : J₀.map s.projection = (D 6).map (MulAut.conj u).toMonoidHom := by
    rw [show J₀ = _ from hj]
    exact himage
  have hRimage : N₀.map s.projection = sylowCarrier.map (MulAut.conj u).toMonoidHom := hN
  have hkJ : s.projection.ker ≤ J₀ := by
    rw [s.projection_kernel]
    let := replacementMoved_normal h d
    exact SmallMover.kernel_le_join _ _ _ 4 (by decide) ((replacement_core_le_radical h d).trans d.radical.le_normalizer)
      (by rw [←moved_centralizer s]; exact le_centralizer_iff.mpr le_rfl)
  let A := (Z d.radical a').comap (embedM d.radical)
  obtain ⟨g,y,hy,hy3,htop₀,htop₁,htop,hJpair⟩ := SylowCompatible.compatible_lifts s.projection s.surjective
    N₀ J₀ (replacementComponent d) A s.component_image
    ((s.projection_kernel.symm ▸ replacement_core_le_radical h d).trans d.radical.le_normalizer) hkJ u hRimage hJimage a ha hswap
  let R₁ := N₀.map (MulAut.conj g).toMonoidHom
  let J₁ := J₀.map (MulAut.conj g).toMonoidHom
  let A₁ := A.map (MulAut.conj y).toMonoidHom
  have hQ : (pCore 2 d.overgroup).map (MulAut.conj g).toMonoidHom = pCore 2 d.overgroup :=
    mem_normalizer_iff_map_conj_eq.mp (by rw [normalizer_eq_top]; exact mem_top g)
  have hU : (replacementMoved d).map (MulAut.conj g).toMonoidHom = replacementMoved d := by
    let := replacementMoved_normal h d
    exact mem_normalizer_iff_map_conj_eq.mp (by rw [normalizer_eq_top]; exact mem_top g)
  let f := (embedM d.radical g)⁻¹
  let x := (embedM d.radical y)⁻¹
  let t := act d.radical f (beta d.radical)
  let N := normalizer (Q d.radical t : Set (FreeAmalgam d.radical)) ⊓
    stabilizer d.radical (alpha d.radical)
  let J := SmallMover.join (U d.radical (alpha d.radical))
    (Q d.radical (alpha d.radical)) N 4
  have hf : f ∈ stabilizer d.radical (alpha d.radical) := by
    change f ∈ stabilizer d.radical (mVertex d.radical 1)
    rw [stabilizer_m_base]
    exact ⟨g⁻¹,by simp only [map_inv,f]⟩
  have ht : N = R₁.map (embedM d.radical) := by
    have hm : (d.radical.map (MulAut.conj g).toMonoidHom).map (embedM d.radical) =
        Q d.radical t := by
      rw [Q_act,Q_beta,SylowCompatible.image_conjugate]
      simp only [f,inv_inv]
    rw [show R₁ = N₀.map (MulAut.conj g).toMonoidHom from rfl,
      map_normalizer_eq_of_bijective _ (MulAut.conj g).bijective,
      SylowNormalizer.normalizer_embed,hm]
  have hJm : J₁.map (embedM d.radical) = J := by
    change ((SmallMover.join (replacementMoved d) (pCore 2 d.overgroup) N₀ 4).map
      (MulAut.conj g).toMonoidHom).map (embedM d.radical) = J
    rw [SmallMover.join_map _ (MulAut.conj g).injective,
      hU,hQ,SmallMover.join_map _ (embedM_injective d.radical),←hc.U_eq_moved,
      ←Q_alpha d.radical (replacement_radical_isPGroup h d) (replacement_core_le_radical h d),←ht]
  have hxL : x ∈ Ltilde d.radical (alpha d.radical) := by
    rw [Ltilde_alpha,replacement_residual h d]
    exact mem_map_of_mem _ ((replacementComponent d).inv_mem hy)
  have hAm : A.map (embedM d.radical) = Z d.radical a' :=
    map_comap_eq_self ((critical_Z_le_stabilizer d.radical (replacementGeometry h d)
      (alpha d.radical) rfl (replacementDistance_pos h d) p.critical).trans_eq
        (stabilizer_m_base d.radical))
  have hA₁m : A₁.map (embedM d.radical) = Z d.radical (act d.radical x a') := by
    rw [SylowCompatible.image_conjugate,hAm,Z_act]
    simp only [x,inv_inv]
  have hrange : (embedM d.radical).range = stabilizer d.radical (alpha d.radical) :=
    (stabilizer_m_base d.radical).symm
  have hpair' : J ⊔ J.map (MulAut.conj x).toMonoidHom = stabilizer d.radical (alpha d.radical) := by
    have hh := congrArg (Subgroup.map (embedM d.radical)) hJpair
    rwa [Subgroup.map_sup,SylowCompatible.image_conjugate (embedM d.radical) J₁ y⁻¹,map_inv,hJm,←MonoidHom.range_eq_map,
      hrange] at hh
  refine ⟨t,?_,x,hxL,?_,?_,?_,?_,hpair',?_⟩
  · have hfix : act d.radical f (alpha d.radical)=alpha d.radical := hf
    rw [←hfix]
    exact (adjacent_act_iff d.radical f _ _).mpr (base_adjacent d.radical)
  · rw [s.projection_kernel] at hy3
    rw [Q_alpha d.radical (replacement_radical_isPGroup h d) (replacement_core_le_radical h d)]
    have hx3 : x^3=embedM d.radical ((y^3)⁻¹) := by simp only [x,inv_pow,map_inv,map_pow]
    rw [hx3]
    exact mem_map_of_mem _ ((pCore 2 d.overgroup).inv_mem hy3)
  · have hh := congrArg (Subgroup.map (embedM d.radical)) htop₀
    rwa [Subgroup.map_sup,←ht,hAm,←MonoidHom.range_eq_map,hrange] at hh
  · have hh := congrArg (Subgroup.map (embedM d.radical)) htop₁
    rwa [Subgroup.map_sup,←ht,hA₁m,←MonoidHom.range_eq_map,hrange] at hh
  · have hh := congrArg (Subgroup.map (embedM d.radical)) htop
    rwa [Subgroup.map_sup,Subgroup.map_sup,hJm,hAm,hA₁m,←MonoidHom.range_eq_map,
      hrange] at hh
  · ext z
    constructor
    · rintro ⟨⟨hz,hzJ⟩,hzJx⟩
      refine ⟨hz,?_⟩
      have hfix : J ⊔ J.map (MulAut.conj x).toMonoidHom ≤ centralizer ({z} : Set _) :=
        sup_le (fun j hj => mem_centralizer_singleton_iff.mpr (hzJ j hj))
          (fun j hj => mem_centralizer_singleton_iff.mpr (hzJx j hj))
      rw [hpair'] at hfix
      exact fun j hj => mem_centralizer_singleton_iff.mp (hfix hj)
    · rintro ⟨hz,hzG⟩
      exact ⟨⟨hz,fun j hj => hzG j (hpair' ▸ mem_sup_left hj)⟩,
        fun j hj => hzG j (hpair' ▸ mem_sup_right hj)⟩

include e hz hn in
/-- The full relative-normalizer mover acts abelianly on the whole seed,
including its central attachment, and preserves every full seed fixer. -/
theorem normalizer_mover_preserves_seed_fixer_knownSimple
    (hb : 4 < replacementDistance h d)
    {a t : Vertex d.radical} (ha : color d.radical a = false)
    (hat : Adjacent d.radical a t) :
    let N := normalizer (Q d.radical t : Set (FreeAmalgam d.radical)) ⊓ stabilizer d.radical a
    let J := SmallMover.join (U d.radical a) (Q d.radical a) N 4
    ⁅J,J⁆ ≤ Q d.radical a ∧
      ∀ A : Subgroup (FreeAmalgam d.radical), A ≤ J →
        J ≤ normalizer ((Z d.radical a ⊓ centralizer (A : Set (FreeAmalgam d.radical)) :
          Subgroup (FreeAmalgam d.radical)) : Set (FreeAmalgam d.radical)) := by
  let s := fullSymmetricAction_knownSimple h e hz hn d (by omega)
  have hc := DistanceTwo.centralLayer_knownSimple G L R h e hz hn d
  let N₀ := normalizer (d.radical : Set d.overgroup)
  let J₀ := SmallMover.join (replacementMoved d) (pCore 2 d.overgroup) N₀ 4
  let N := normalizer (Q d.radical t : Set (FreeAmalgam d.radical)) ⊓ stabilizer d.radical a
  let J := SmallMover.join (U d.radical a) (Q d.radical a) N 4
  obtain ⟨u,_,_,hJ,himage,_⟩ := SylowSmallMovers.normalizer_small_movers_knownSimple
    (e := e) (hz := hz) (hn := hn) hb
  have him : J₀.map s.projection = (D 6).map (MulAut.conj u).toMonoidHom := by
    rw [show J₀ = _ from hJ]
    exact himage
  have hbase : ⁅J₀,J₀⁆ ≤ pCore 2 d.overgroup := by
    rw [←s.projection_kernel,←Subgroup.map_eq_bot_iff,map_commutator,him]
    let : IsElementaryAbelian 2 (D 6) := elementary_disjointTranspositions (3 : Fin 4)
    let helem : IsElementaryAbelian 2 ((D 6).map (MulAut.conj u).toMonoidHom) :=
      IsElementaryAbelian.map _
    exact commutator_eq_bot_iff_le_centralizer.mpr
      (le_centralizer_iff_isMulCommutative.mpr helem.toIsMulCommutative)
  obtain ⟨i,hi,hir,hiR,hiQ,hiU⟩ := SylowAdjacent.edge_coordinates (h := h) hc ha hat
  have hiN : N₀.map i = N := by
    have hh : (normalizer (d.radical.map i : Set _)).comap i = N₀ := by
      rw [comap_normalizer_eq_of_le_range (map_le_range _ _),comap_map_eq_self_of_injective hi]
    rw [←hh,map_comap_eq,hiR,hir,inf_comm]
  have hiJ : J₀.map i = J := by
    rw [SmallMover.join_map i hi,hiU,hiQ,hiN]
  have hderived : ⁅J,J⁆ ≤ Q d.radical a := by
    have hh := map_mono (f := i) hbase
    rwa [map_commutator,hiJ,hiQ] at hh
  have hJG : J ≤ stabilizer d.radical a :=
    (SmallMover.join_le _ _ _ _).trans inf_le_right
  refine ⟨hderived,fun A hA => ?_⟩
  exact CubePairedKernel.abelian_action_preserves_fixed J (Z d.radical a) A
    (hJG.trans (Z_normalized d.radical a)) hA
    (hderived.trans (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp
      (Z_centralizes_Q d.radical a ha))))


/-- The small mover of the full relative normalizer at a literal incident edge. -/
abbrev relativeMover (a t : Vertex d.radical) : Subgroup (FreeAmalgam d.radical) :=
  SmallMover.join (U d.radical a) (Q d.radical a)
    (normalizer (Q d.radical t : Set (FreeAmalgam d.radical)) ⊓ stabilizer d.radical a) 4

include e hz hn in
private theorem relativeMover_core_le
    (hb : 4 < replacementDistance h d)
    {a t : Vertex d.radical} (ha : color d.radical a = false)
    (hat : Adjacent d.radical a t) : Q d.radical a ≤ relativeMover (d := d) a t := by
  obtain ⟨J,_,hj,hQ,_⟩ := SylowSmallMovers.edge_normalizer_small_movers_knownSimple
    (e := e) (hz := hz) (hn := hn) hb ha hat
  exact hQ.trans_eq hj.symm

omit [Finite G] in
private theorem relativeMover_le_stabilizer (a t : Vertex d.radical) :
    relativeMover (d := d) a t ≤ stabilizer d.radical a :=
  (SmallMover.join_le _ _ _ _).trans inf_le_right

include e hz hn in
/-- The paired small movers put the common full-kernel fixer in the actual
Baumann slice. The edge core need not act abelianly on the full seed. -/
theorem paired_trapped_fixer_le_slice_knownSimple
    (hb : 4 < replacementDistance h d)
    {a z w c t : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a z)
    (q : CriticalPath d.radical (replacementGeometry h d) a w)
    (hps : (Q d.radical z).relIndex (Z d.radical a) < 4)
    (hqs : (Q d.radical w).relIndex (Z d.radical a) < 4)
    (hat : Adjacent d.radical a t) (hct : Adjacent d.radical c t)
    (hequal : relativeMover (d := d) c t =
      relativeMover (d := d) a t)
    (hgen : relativeMover (d := d) c t ⊔
      Z d.radical z ⊔ Z d.radical w = stabilizer d.radical a)
    (hpbad : Z d.radical c ≤ Q d.radical (p.walk.getVert (p.walk.length-2)))
    (hqbad : Z d.radical c ≤ Q d.radical (q.walk.getVert (q.walk.length-2))) :
    Z d.radical c ⊓ centralizer
      ((Z d.radical z ⊓ Q d.radical a ⊔ Z d.radical w ⊓ Q d.radical a :
        Subgroup (FreeAmalgam d.radical)) : Set (FreeAmalgam d.radical)) ≤
      B d.radical a ((replacementGeometry h d).Z_normal _) := by
  have hb2 : 2 < replacementDistance h d := by omega
  let s := fullSymmetricAction_knownSimple h e hz hn d hb2
  have hc := DistanceTwo.centralLayer_knownSimple G L R h e hz hn d
  let A := Z d.radical z ⊓ Q d.radical a ⊔ Z d.radical w ⊓ Q d.radical a
  let F := Z d.radical c ⊓ centralizer (A : Set (FreeAmalgam d.radical))
  let Y := F ⊔ Z d.radical a
  let J := relativeMover (d := d) c t
  have hcol : color d.radical c = false := by
    have h1 := adjacent_color_ne d.radical hat
    have h2 := adjacent_color_ne d.radical hct
    rw [p.start_color] at h1
    have ht : color d.radical t = true := by
      cases he : color d.radical t
      · exact (h1 he.symm).elim
      · rfl
    cases he : color d.radical c
    · rfl
    · exact (h2 (he.trans ht.symm)).elim
  have hdist : (cosetGraph d.radical).dist c a ≤ 2 := by
    have h1 : (cosetGraph d.radical).dist c t = 1 :=
      SimpleGraph.dist_eq_one_iff_adj.mpr ((cosetGraph_adj d.radical _ _).mpr hct)
    have h2 : (cosetGraph d.radical).dist t a = 1 :=
      SimpleGraph.dist_eq_one_iff_adj.mpr ((cosetGraph_adj d.radical _ _).mpr (adjacent_symm d.radical hat))
    simpa only [h1,h2] using (cosetGraph_connected d.radical).dist_triangle
      (u := c) (v := t) (w := a)
  have hZV : Z d.radical c ≤ V d.radical a :=
    (Z_le_localZSpan d.radical _ _).trans (localZSpan_le_V d.radical hdist)
  have hVG : V d.radical a ≤ stabilizer d.radical a :=
    (replacementGeometry h d).V_local a p.start_color (by
      rw [(replacementGeometry h d).distance_constant a p.start_color]; exact hb2)
  have hQJ : Q d.radical a ≤ J := by
    change Q d.radical a ≤ relativeMover (d := d) c t
    rw [hequal]
    exact relativeMover_core_le (e := e) (hz := hz) (hn := hn) hb p.start_color hat
  have hFt : J ≤ normalizer (F : Set (FreeAmalgam d.radical)) :=
    (normalizer_mover_preserves_seed_fixer_knownSimple (e := e) (hz := hz) (hn := hn)
      hb hcol hct).2 A ((sup_le inf_le_right inf_le_right).trans hQJ)
  have hmove {v : Vertex d.radical}
      (r : CriticalPath d.radical (replacementGeometry h d) a v)
      (hrs : (Q d.radical v).relIndex (Z d.radical a) < 4)
      (hrbad : Z d.radical c ≤ Q d.radical (r.walk.getVert (r.walk.length-2)))
      (hA : Z d.radical v ⊓ Q d.radical a ≤ A) :
      Z d.radical v ≤ normalizer (Y : Set (FreeAmalgam d.radical)) := by
    have hFmove : ⁅F,Z d.radical v⁆ ≤ Z d.radical a :=
      small_critical_predecessor_commutator s hc hb2 r hrs F (inf_le_left.trans hrbad)
        (inf_le_right.trans (centralizer_le hA))
    have hYmove : ⁅Y,Z d.radical v⁆ ≤ Z d.radical a :=
      commutator_sup_le_of_relative_normal (stabilizer d.radical a)
        F (Z d.radical a) (Z d.radical v) (Z d.radical a)
        (Z_normalized d.radical a) ((inf_le_left.trans hZV).trans hVG)
        (Z_le_stabilizer d.radical a) hFmove
        (((critical_Z_commutator_le_moving (h := h) r).trans inf_le_left).trans
          (DistanceEight.U_le_Z d.radical a))
    exact le_normalizer_iff_commutator_le_left.mpr (hYmove.trans le_sup_right)
  have hJG : J ≤ stabilizer d.radical a := by
    rw [←hgen]
    exact le_sup_left.trans le_sup_left
  have hYN : stabilizer d.radical a ≤ normalizer (Y : Set (FreeAmalgam d.radical)) := by
    rw [←hgen]
    refine sup_le (sup_le ?_ (hmove p hps hpbad le_sup_left)) (hmove q hqs hqbad le_sup_right)
    exact (le_inf hFt (hJG.trans (Z_normalized d.radical a))).trans
      (normalizer_inf_normalizer_le_normalizer_sup _ _)
  have hYV : Y ≤ V d.radical a := sup_le (inf_le_left.trans hZV) (Z_le_VBall d.radical a 2)
  have hYprod : Y ≤ Z d.radical c ⊔ Z d.radical a := sup_le_sup inf_le_left le_rfl
  let := finite_stabilizer d.radical a
  let : Finite (Z d.radical c ⊔ Z d.radical a : Subgroup (FreeAmalgam d.radical)) :=
    Finite.of_injective
      (inclusion (sup_le (hZV.trans hVG) (Z_le_stabilizer d.radical a))) (inclusion_injective _)
  have hindex : (Z d.radical a).relIndex Y ≤ 8 :=
    (relIndex_le_of_le_right hYprod index_ne_zero_of_finite).trans
      (SylowSpanSelection.adjacent_seed_span_index_le_eight
        (e := e) (hz := hz) (hn := hn) hb p.start_color hat hct)
  exact le_sup_left.trans
    (SylowSpanSelection.normal_small_radius_le_slice_at s hb2 p.start_color Y hYV hYN hindex)

include e hz hn in
/-- A strict slice forces the simultaneous paired kernel commutator to have
order greater than two, with the same two kernels and the same selected seed. -/
theorem paired_trapped_joint_movement_gt_two_knownSimple
    (hb : 4 < replacementDistance h d)
    {a z w c t : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a z)
    (q : CriticalPath d.radical (replacementGeometry h d) a w)
    (hps : (Q d.radical z).relIndex (Z d.radical a) < 4)
    (hqs : (Q d.radical w).relIndex (Z d.radical a) < 4)
    (hat : Adjacent d.radical a t) (hct : Adjacent d.radical c t)
    (hequal : relativeMover (d := d) c t =
      relativeMover (d := d) a t)
    (hgen : relativeMover (d := d) c t ⊔
      Z d.radical z ⊔ Z d.radical w = stabilizer d.radical a)
    (hpbad : Z d.radical c ≤ Q d.radical (p.walk.getVert (p.walk.length-2)))
    (hqbad : Z d.radical c ≤ Q d.radical (q.walk.getVert (q.walk.length-2)))
    (hindex : 2 < (B d.radical a ((replacementGeometry h d).Z_normal _)).relIndex
      (U d.radical c)) :
    2 < Nat.card (⁅U d.radical c,Z d.radical z ⊓ Q d.radical a ⊔
      Z d.radical w ⊓ Q d.radical a⁆ : Subgroup (FreeAmalgam d.radical)) := by
  by_contra! hbound
  let s := fullSymmetricAction_knownSimple h e hz hn d (by omega)
  have hc := DistanceTwo.centralLayer_knownSimple G L R h e hz hn d
  let A := Z d.radical z ⊓ Q d.radical a ⊔ Z d.radical w ⊓ Q d.radical a
  have ht : color d.radical t = true := by
    have hh := adjacent_color_ne d.radical hat
    rw [p.start_color] at hh
    cases he : color d.radical t
    · exact (hh he.symm).elim
    · rfl
  have hcol : color d.radical c = false := by
    have hh := adjacent_color_ne d.radical hct
    rw [ht] at hh
    cases he : color d.radical c
    · rfl
    · exact (hh he).elim
  have hAG : A ≤ stabilizer d.radical c :=
    ((sup_le inf_le_right inf_le_right).trans (Q_le_adjacent_h d.radical ht hat)).trans
      (fun _ hx => hx.2 _ (adjacent_symm d.radical hct))
  have hi := moving_small_commutator_fixed_index s hc hcol A hAG hbound
  have hFB := paired_trapped_fixer_le_slice_knownSimple (e := e) (hz := hz) (hn := hn)
    hb p q hps hqs hat hct hequal hgen hpbad hqbad
  let := finite_Z d.radical c
  let : Finite (U d.radical c) := Finite.of_injective
    (inclusion (DistanceEight.U_le_Z d.radical c)) (inclusion_injective _)
  have hh := relIndex_le_of_le_left
    ((inf_le_inf_right _ (DistanceEight.U_le_Z d.radical c)).trans hFB)
    (index_ne_zero_of_finite (H := (U d.radical c ⊓ centralizer
      (A : Set (FreeAmalgam d.radical))).subgroupOf (U d.radical c)))
  rw [inf_relIndex_left] at hh
  exact (Nat.not_le_of_gt hindex) (hh.trans hi)


include e hz hn in
private theorem relativeMover_full_seed_quadratic
    (hb : 4 < replacementDistance h d)
    {a t : Vertex d.radical} (ha : color d.radical a = false)
    (hat : Adjacent d.radical a t)
    (hgen : X d.radical a = U d.radical a ⊔
      (X d.radical a ⊓ centralizer (stabilizer d.radical a : Set (FreeAmalgam d.radical)))) :
    ⁅⁅Z d.radical a,relativeMover (d := d) a t⁆,relativeMover (d := d) a t⁆ = ⊥ := by
  let J := relativeMover (d := d) a t
  let C := X d.radical a ⊓ centralizer (stabilizer d.radical a : Set (FreeAmalgam d.radical))
  have hX := SylowPairedFixer.central_generation_eq_seed (h := h) ha hat hgen
  have hJ := relativeMover_le_stabilizer (d := d) a t
  have hC : C ≤ centralizer (J : Set (FreeAmalgam d.radical)) :=
    inf_le_right.trans (centralizer_le hJ)
  have hCn : C ≤ normalizer (U d.radical a : Set (FreeAmalgam d.radical)) :=
    (inf_le_left.trans ((omegaCenter_le _).trans
      (show Q d.radical a ≤ stabilizer d.radical a from fun _ hx => hx.1))).trans (U_normalized a)
  change ⁅⁅Z d.radical a,J⁆,J⁆ = ⊥
  rw [←hX,hgen,commutator_sup_fixed _ C J hCn hC]
  exact SylowAdjacent.edge_small_mover_quadratic_knownSimple
    (e := e) (hz := hz) (hn := hn) hb ha hat

include e hz hn in
/-- Once the nonnormalizing trapped pair has supplied X = Z, equal neighboring
small movers put their entire neighbor-seed commutator in their central omega.
That omega is exactly the full starting-seed fixer, with all central elements. -/
theorem equal_mover_omega_control_knownSimple
    (hb : 4 < replacementDistance h d)
    {a c t : Vertex d.radical} (ha : color d.radical a = false)
    (hat : Adjacent d.radical a t) (hct : Adjacent d.radical c t)
    (hequal : relativeMover (d := d) c t =
      relativeMover (d := d) a t)
    (hXgen : X d.radical a = U d.radical a ⊔
      (X d.radical a ⊓ centralizer (stabilizer d.radical a : Set (FreeAmalgam d.radical)))) :
    let J := relativeMover (d := d) a t
    omegaCenter J = Z d.radical a ⊓ centralizer (J : Set (FreeAmalgam d.radical)) ∧
      ⁅Z d.radical c,J⁆ ≤ omegaCenter J := by
  have hX := SylowPairedFixer.central_generation_eq_seed (h := h) ha hat hXgen
  let s := fullSymmetricAction_knownSimple h e hz hn d (by omega)
  have hc := DistanceTwo.centralLayer_knownSimple G L R h e hz hn d
  let J := relativeMover (d := d) a t
  have hcol : color d.radical c = false := by
    have h1 := adjacent_color_ne d.radical hat
    have h2 := adjacent_color_ne d.radical hct
    rw [ha] at h1
    have ht : color d.radical t = true := by
      cases he : color d.radical t
      · exact (h1 he.symm).elim
      · rfl
    cases he : color d.radical c
    · rfl
    · exact (h2 (he.trans ht.symm)).elim
  have hQJ := relativeMover_core_le (e := e) (hz := hz) (hn := hn) hb ha hat
  have hQcJ : Q d.radical c ≤ J := by
    change Q d.radical c ≤ relativeMover (d := d) a t
    rw [←hequal]
    exact relativeMover_core_le (e := e) (hz := hz) (hn := hn) hb hcol hct
  have hJG : J ≤ stabilizer d.radical a :=
    relativeMover_le_stabilizer (d := d) a t
  have hJGc : J ≤ stabilizer d.radical c := by
    change relativeMover (d := d) a t ≤ _
    rw [←hequal]
    exact relativeMover_le_stabilizer (d := d) c t
  have hZQ : Z d.radical a ≤ Q d.radical a := hX.ge.trans (omegaCenter_le _)
  have hZcX : Z d.radical c ≤ X d.radical c := by
    apply (replacementGeometry h d).omega_bound c hcol
    rw [(replacementGeometry h d).distance_constant c hcol]
    exact replacementDistance_pos h d
  have hOmegaZ : omegaCenter J ≤ Z d.radical a := by
    rw [←hX]
    intro x hx
    obtain ⟨hxJ,hx2,hxc⟩ := mem_omegaCenter_iff.mp hx
    have hxQ : x ∈ Q d.radical a := by
      rw [←C_eq_Q s hc a ha]
      exact ⟨hJG hxJ,fun y hy => hxc y (hQJ (hZQ hy))⟩
    exact mem_omegaCenter_iff.mpr ⟨hxQ,hx2,fun y hy => hxc y (hQJ hy)⟩
  have hquad : ⁅⁅Z d.radical c,J⁆,J⁆ = ⊥ := by
    have hh := relativeMover_full_seed_quadratic (e := e) (hz := hz) (hn := hn) hb hcol hct
      (X_central_generation_all ha hXgen c hcol)
    rwa [hequal] at hh
  have hcommZ : ⁅Z d.radical c,J⁆ ≤ Z d.radical c :=
    le_normalizer_iff_commutator_le_left.mp (hJGc.trans (Z_normalized d.radical c))
  have hcommJ : ⁅Z d.radical c,J⁆ ≤ J :=
    (hcommZ.trans hZcX).trans ((omegaCenter_le _).trans hQcJ)
  have hcommC : ⁅Z d.radical c,J⁆ ≤ centralizer (J : Set (FreeAmalgam d.radical)) :=
    commutator_eq_bot_iff_le_centralizer.mp hquad
  refine ⟨le_antisymm (le_inf hOmegaZ ?_) ?_,?_⟩
  · intro x hx
    exact (mem_omegaCenter_iff.mp hx).2.2
  · intro x hx
    exact mem_omegaCenter_iff.mpr ⟨hQJ (hZQ hx.1),
      (mem_omegaCenter_iff.mp (hX.ge hx.1)).2.1,hx.2⟩
  · intro x hx
    exact mem_omegaCenter_iff.mpr ⟨hcommJ hx,
      (mem_omegaCenter_iff.mp (hZcX (hcommZ hx))).2.1,hcommC hx⟩

include e hz hn in
private theorem equal_mover_pair_control
    (hb : 4 < replacementDistance h d)
    {a c t : Vertex d.radical} (ha : color d.radical a = false)
    (hat : Adjacent d.radical a t) (hct : Adjacent d.radical c t)
    (hequal : relativeMover (d := d) c t =
      relativeMover (d := d) a t)
    (hXgen : X d.radical a = U d.radical a ⊔
      (X d.radical a ⊓ centralizer (stabilizer d.radical a : Set (FreeAmalgam d.radical))))
    (x : FreeAmalgam d.radical) (hx : x ∈ stabilizer d.radical a)
    (hpair : relativeMover (d := d) c t ⊔
      (relativeMover (d := d) c t).map
        (MulAut.conj x).toMonoidHom = stabilizer d.radical a)
    (A : Subgroup (FreeAmalgam d.radical)) (hA : A ≤ Q d.radical a) :
    ⁅Z d.radical c,A⁆ ≤ Z d.radical a ∧
      ⁅Z d.radical c,A⁆ ⊓ ⁅Z d.radical (act d.radical x⁻¹ c),A⁆ ≤
        Z d.radical a ⊓ centralizer (stabilizer d.radical a : Set (FreeAmalgam d.radical)) := by
  let J := relativeMover (d := d) a t
  have hQJ := relativeMover_core_le (e := e) (hz := hz) (hn := hn) hb ha hat
  obtain ⟨hOmega,hcomm⟩ := equal_mover_omega_control_knownSimple
    (e := e) (hz := hz) (hn := hn) hb ha hat hct hequal hXgen
  have hcore : ⁅Z d.radical c,Q d.radical a⁆ ≤
      Z d.radical a ⊓ centralizer (J : Set (FreeAmalgam d.radical)) :=
    (commutator_mono le_rfl hQJ).trans (hcomm.trans_eq hOmega)
  have hQa : (Q d.radical a).map (MulAut.conj x).toMonoidHom = Q d.radical a :=
    mem_normalizer_iff_map_conj_eq.mp (Q_normalized d.radical a hx)
  have hZa : (Z d.radical a).map (MulAut.conj x).toMonoidHom = Z d.radical a :=
    mem_normalizer_iff_map_conj_eq.mp (Z_normalized d.radical a hx)
  have hcore₂ : ⁅Z d.radical (act d.radical x⁻¹ c),Q d.radical a⁆ ≤
      Z d.radical a ⊓ centralizer
        (J.map (MulAut.conj x).toMonoidHom : Set (FreeAmalgam d.radical)) := by
    have hh := map_mono (f := (MulAut.conj x).toMonoidHom) hcore
    rw [map_commutator,←map_inf_centralizer_of_injective _ (MulAut.conj x).injective,hQa,hZa] at hh
    simpa only [Z_act,inv_inv] using hh
  have h₁ := (commutator_mono le_rfl hA).trans hcore
  have h₂ := (commutator_mono le_rfl hA).trans hcore₂
  refine ⟨h₁.trans inf_le_left,le_inf (inf_le_left.trans (h₁.trans inf_le_left)) ?_⟩
  apply le_centralizer_iff.mpr
  rw [hequal] at hpair
  rw [←hpair]
  exact sup_le (le_centralizer_iff.mp (inf_le_left.trans (h₁.trans inf_le_right)))
    (le_centralizer_iff.mp (inf_le_right.trans (h₂.trans inf_le_right)))
include e hz hn in
private theorem paired_traps_impossible_of_nonnormal
    (hb : 4 < replacementDistance h d)
    {a z c t : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a z)
    (hsmall : (Q d.radical z).relIndex (Z d.radical a) < 4)
    (hat : Adjacent d.radical a t) (hct : Adjacent d.radical c t)
    (hequal : relativeMover (d := d) c t =
      relativeMover (d := d) a t)
    (x : FreeAmalgam d.radical) (hx : x ∈ stabilizer d.radical a)
    (q : CriticalPath d.radical (replacementGeometry h d) a (act d.radical x z))
    (hq : ∀ i, q.walk.getVert i = act d.radical x (p.walk.getVert i))
    (hqs : (Q d.radical (act d.radical x z)).relIndex (Z d.radical a) < 4)
    (hgen : relativeMover (d := d) c t ⊔
      Z d.radical z ⊔ Z d.radical (act d.radical x z) = stabilizer d.radical a)
    (hpair : relativeMover (d := d) c t ⊔
      (relativeMover (d := d) c t).map
        (MulAut.conj x).toMonoidHom = stabilizer d.radical a)
    (hpbad : Z d.radical c ≤ Q d.radical (p.walk.getVert (p.walk.length-2)))
    (hqbad : Z d.radical c ≤ Q d.radical (q.walk.getVert (q.walk.length-2)))
    (hnorm : ¬ Z d.radical z ≤ normalizer
      ((Z d.radical c ⊔ Z d.radical a : Subgroup (FreeAmalgam d.radical)) :
        Set (FreeAmalgam d.radical)))
    (hindex : 2 < (B d.radical a ((replacementGeometry h d).Z_normal _)).relIndex
      (U d.radical c)) : False := by
  have hb2 : 2 < replacementDistance h d := by omega
  let s := fullSymmetricAction_knownSimple h e hz hn d hb2
  have hc := DistanceTwo.centralLayer_knownSimple G L R h e hz hn d
  let F := Z d.radical z ⊓ Q d.radical a
  let F₂ := Z d.radical (act d.radical x z) ⊓ Q d.radical a
  let C₂ := Z d.radical (act d.radical x⁻¹ c)
  let P := Z d.radical a ⊔ Z d.radical c ⊔ C₂
  let K := ⁅P,F⁆
  have hQa : (Q d.radical a).map (MulAut.conj x).toMonoidHom = Q d.radical a :=
    mem_normalizer_iff_map_conj_eq.mp (Q_normalized d.radical a hx)
  have hZa : (Z d.radical a).map (MulAut.conj x).toMonoidHom = Z d.radical a :=
    mem_normalizer_iff_map_conj_eq.mp (Z_normalized d.radical a hx)
  have hC₂ : C₂ = (Z d.radical c).map (MulAut.conj x).toMonoidHom := by
    simp only [C₂,Z_act,inv_inv]
  have hCV := neighbor_seed_le_radius hat hct
  have hC₂V : C₂ ≤ V d.radical a := by
    have hh := map_mono (f := (MulAut.conj x).toMonoidHom) hCV
    have he : (V d.radical a).map (MulAut.conj x).toMonoidHom = V d.radical a :=
      mem_normalizer_iff_map_conj_eq.mp (DistanceEight.V_normalized d.radical a hx)
    rwa [←hC₂,he] at hh
  have hAV : Z d.radical a ≤ V d.radical a := Z_le_VBall d.radical a 2
  have hVG := (replacementGeometry h d).V_local a p.start_color (by
    rw [(replacementGeometry h d).distance_constant a p.start_color]; exact hb2)
  have hlast := critical_last_edge_inputs (h := h) hb2 p
  have hC₂pre : C₂ ≤ Q d.radical (p.walk.getVert (p.walk.length-2)) := by
    have hh := map_mono (f := (MulAut.conj x).toMonoidHom) hqbad
    have hlen : q.walk.length = p.walk.length := q.length_eq_b.trans p.length_eq_b.symm
    rw [hlen,hq] at hh
    have he := Q_act d.radical x⁻¹ (act d.radical x (p.walk.getVert (p.walk.length-2)))
    simp only [inv_inv,←act_mul,mul_inv_cancel,act_one] at he
    rwa [←hC₂,←he] at hh
  have hPt : P ≤ Q d.radical (p.walk.getVert (p.walk.length-1)) :=
    sup_le (sup_le hlast.2.2 (hpbad.trans hlast.2.1)) (hC₂pre.trans hlast.2.1)
  have hpreG : Q d.radical (p.walk.getVert (p.walk.length-2)) ≤ stabilizer d.radical z :=
    hlast.2.1.trans (fun _ hv => hv.2 _ (adjacent_symm d.radical hlast.1))
  have hXz := (SylowPairedFixer.trapped_nonnormalized_full_kernel_knownSimple
    (e := e) (hz := hz) (hn := hn) hb2 p hsmall hat hct hpbad hnorm).1
  have hXgen := X_central_generation_all p.end_color hXz a p.start_color
  have hcontrol := equal_mover_pair_control
    (e := e) (hz := hz) (hn := hn) hb p.start_color hat hct hequal hXgen x hx hpair
    (Q d.radical a) le_rfl
  have hC₂Q : ⁅C₂,Q d.radical a⁆ ≤ Z d.radical a := by
    have hh := map_mono (f := (MulAut.conj x).toMonoidHom) hcontrol.1
    rwa [map_commutator,←hC₂,hQa,hZa] at hh
  have hK : K ≤ Z d.radical a := by
    apply commutator_sup_le_of_relative_normal (stabilizer d.radical a)
      (Z d.radical a ⊔ Z d.radical c) C₂ F (Z d.radical a)
      (Z_normalized d.radical a) ((sup_le hAV hCV).trans hVG) (hC₂V.trans hVG)
    · apply commutator_sup_le_of_relative_normal (stabilizer d.radical a)
        (Z d.radical a) (Z d.radical c) F (Z d.radical a)
        (Z_normalized d.radical a) (Z_le_stabilizer d.radical a) (hCV.trans hVG)
      · exact (commutator_mono le_rfl inf_le_right).trans_eq
          (Z_centralizes_Q d.radical a p.start_color) |>.trans bot_le
      · exact (commutator_mono le_rfl inf_le_right).trans hcontrol.1
    · exact (commutator_mono le_rfl inf_le_right).trans hC₂Q
  have hcol : color d.radical c = false := by
    have h1 := adjacent_color_ne d.radical hat
    have h2 := adjacent_color_ne d.radical hct
    rw [p.start_color] at h1
    have ht : color d.radical t = true := by
      cases he : color d.radical t
      · exact (h1 he.symm).elim
      · rfl
    cases he : color d.radical c
    · rfl
    · exact (h2 (he.trans ht.symm)).elim
  let := (replacementGeometry h d).Z_elementary (replacementDistance_pos h d) a p.start_color
  let := (replacementGeometry h d).Z_elementary (replacementDistance_pos h d) c hcol
  let : IsElementaryAbelian 2 C₂ := hC₂ ▸ IsElementaryAbelian.map (MulAut.conj x).toMonoidHom
  have hVV : V d.radical a ≤ centralizer (V d.radical a : Set (FreeAmalgam d.radical)) :=
    le_centralizer_iff_isMulCommutative.mpr (V_abelian_of_four_lt d.radical p.start_color hb)
  let : IsElementaryAbelian 2 (Z d.radical a ⊔ Z d.radical c : Subgroup (FreeAmalgam d.radical)) :=
    IsElementaryAbelian.sup_of_le_centralizer (hCV.trans (hVV.trans (centralizer_le hAV)))
  have hel : IsElementaryAbelian 2 P := IsElementaryAbelian.sup_of_le_centralizer
    (hC₂V.trans (hVV.trans (centralizer_le (sup_le hAV hCV))))
  have hbound : Nat.card K ≤ 2 := combined_actor_kernel_card_le_two s hc hb2 p hsmall
    P hel (le_sup_left.trans le_sup_left) (le_sup_right.trans le_sup_left) hCV hPt hK hnorm
  have hne₁ := nonnormalizing_seed_kernel_ne_bot s hc hb2 p hsmall hCV
    (hpbad.trans hpreG) hnorm
  have h₁ : ⁅Z d.radical c,F⁆ ≤ K := commutator_mono (le_sup_right.trans le_sup_left) le_rfl
  have h₂ : ⁅C₂,F⁆ ≤ K := commutator_mono le_sup_right le_rfl
  let := finite_Z d.radical a
  let : Finite K := Finite.of_injective (inclusion hK) (inclusion_injective _)
  have hlarge := paired_trapped_joint_movement_gt_two_knownSimple
    (e := e) (hz := hz) (hn := hn) hb p q hsmall hqs hat hct hequal hgen hpbad hqbad hindex
  -- The source zero-commutator subcase: it would bound joint movement by K.
  have hne₂ : ⁅C₂,F⁆ ≠ ⊥ := by
    intro hzero
    have hzero₂ : ⁅Z d.radical c,F₂⁆ = ⊥ := by
      have hh := congrArg (Subgroup.map (MulAut.conj x⁻¹).toMonoidHom) hzero
      have hCback : C₂.map (MulAut.conj x⁻¹).toMonoidHom = Z d.radical c := by
        dsimp only [C₂]
        rw [←Z_act,←act_mul,inv_mul_cancel,act_one]
      have hFback : F.map (MulAut.conj x⁻¹).toMonoidHom = F₂ := by
        have he : (Q d.radical a).map (MulAut.conj x⁻¹).toMonoidHom = Q d.radical a :=
          mem_normalizer_iff_map_conj_eq.mp
            (Q_normalized d.radical a ((stabilizer d.radical a).inv_mem hx))
        dsimp only [F,F₂]
        rw [Subgroup.map_inf _ _ _ (MulAut.conj x⁻¹).injective,←Z_act,he]
      rwa [map_commutator,hCback,hFback,Subgroup.map_bot] at hh
    have hNK : Q d.radical a ≤ normalizer (K : Set (FreeAmalgam d.radical)) :=
      ((le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp
        (Z_centralizes_Q d.radical a p.start_color))).trans
          (centralizer_le hK)).trans (Subgroup.centralizer_le_normalizer _)
    have hjoin : ⁅F ⊔ F₂,Z d.radical c⁆ ≤ K :=
      commutator_sup_le_of_relative_normal (Q d.radical a) F F₂ (Z d.radical c) K
        hNK inf_le_right inf_le_right
        (by rw [commutator_comm]; exact h₁)
        (by rw [commutator_comm,hzero₂]; exact bot_le)
    have hU : ⁅U d.radical c,F ⊔ F₂⁆ ≤ K := by
      rw [commutator_comm] at hjoin
      exact (commutator_mono (DistanceEight.U_le_Z d.radical c) le_rfl).trans hjoin
    exact (Nat.not_le_of_gt hlarge) ((card_le_of_le hU).trans hbound)

  let : Finite (⁅Z d.radical c,F⁆ : Subgroup (FreeAmalgam d.radical)) :=
    Finite.of_injective (inclusion h₁) (inclusion_injective _)
  let : Finite (⁅C₂,F⁆ : Subgroup (FreeAmalgam d.radical)) :=
    Finite.of_injective (inclusion h₂) (inclusion_injective _)
  have hpos₁ : 1 < Nat.card (⁅Z d.radical c,F⁆ : Subgroup (FreeAmalgam d.radical)) :=
    (one_lt_card_iff_ne_bot _).mpr hne₁
  have hpos₂ : 1 < Nat.card (⁅C₂,F⁆ : Subgroup (FreeAmalgam d.radical)) :=
    (one_lt_card_iff_ne_bot _).mpr hne₂
  have heq₁ : ⁅Z d.radical c,F⁆ = K := eq_of_le_of_card_ge h₁ (by omega)
  have heq₂ : ⁅C₂,F⁆ = K := eq_of_le_of_card_ge h₂ (by omega)
  have hcentral : K ≤ centralizer (stabilizer d.radical a : Set (FreeAmalgam d.radical)) := by
    have hh := (equal_mover_pair_control
      (e := e) (hz := hz) (hn := hn) hb p.start_color hat hct hequal hXgen x hx hpair F inf_le_right).2
    change ⁅Z d.radical c,F⁆ ⊓ ⁅C₂,F⁆ ≤ _ at hh
    rw [heq₁,heq₂,inf_idem] at hh
    exact hh.trans inf_le_right
  have hMK : stabilizer d.radical a ≤ normalizer (K : Set (FreeAmalgam d.radical)) :=
    (le_centralizer_iff.mp hcentral).trans (Subgroup.centralizer_le_normalizer _)
  have hmapK : K.map (MulAut.conj x⁻¹).toMonoidHom = K :=
    mem_normalizer_iff_map_conj_eq.mp (hMK ((stabilizer d.radical a).inv_mem hx))
  have hmapC : C₂.map (MulAut.conj x⁻¹).toMonoidHom = Z d.radical c := by
    dsimp only [C₂]
    rw [←Z_act,←act_mul,inv_mul_cancel,act_one]
  have hmapF : F.map (MulAut.conj x⁻¹).toMonoidHom = F₂ := by
    have he : (Q d.radical a).map (MulAut.conj x⁻¹).toMonoidHom = Q d.radical a :=
      mem_normalizer_iff_map_conj_eq.mp (Q_normalized d.radical a ((stabilizer d.radical a).inv_mem hx))
    dsimp only [F,F₂]
    rw [Subgroup.map_inf _ _ _ (MulAut.conj x⁻¹).injective,←Z_act,he]
  have heq₃ : ⁅Z d.radical c,F₂⁆ = K := by
    have hh := congrArg (Subgroup.map (MulAut.conj x⁻¹).toMonoidHom) heq₂
    rwa [map_commutator,hmapC,hmapF,hmapK] at hh
  have hjoin : ⁅F ⊔ F₂,Z d.radical c⁆ ≤ K :=
    commutator_sup_le_of_relative_normal (stabilizer d.radical a) F F₂ (Z d.radical c) K
      hMK (inf_le_right.trans (show Q d.radical a ≤ stabilizer d.radical a from fun _ hv => hv.1))
      (inf_le_right.trans (show Q d.radical a ≤ stabilizer d.radical a from fun _ hv => hv.1))
      (by rw [commutator_comm]; exact heq₁.le) (by rw [commutator_comm]; exact heq₃.le)
  have hU : ⁅U d.radical c,F ⊔ F₂⁆ ≤ K := by
    rw [commutator_comm] at hjoin
    exact (commutator_mono (DistanceEight.U_le_Z d.radical c) le_rfl).trans hjoin
  exact (Nat.not_le_of_gt hlarge) ((card_le_of_le hU).trans hbound)

include e hz hn in
/-- Equal relative movers exclude simultaneous trapping. The proof also
handles a zero second commutator, and does not assume two nonnormalizing seeds. -/
theorem paired_traps_impossible_knownSimple
    (hb : 4 < replacementDistance h d)
    {a z c t : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a z)
    (hsmall : (Q d.radical z).relIndex (Z d.radical a) < 4)
    (hat : Adjacent d.radical a t) (hct : Adjacent d.radical c t)
    (hequal : relativeMover (d := d) c t = relativeMover (d := d) a t)
    (x : FreeAmalgam d.radical) (hx : x ∈ stabilizer d.radical a)
    (q : CriticalPath d.radical (replacementGeometry h d) a (act d.radical x z))
    (hq : ∀ i, q.walk.getVert i = act d.radical x (p.walk.getVert i))
    (hqs : (Q d.radical (act d.radical x z)).relIndex (Z d.radical a) < 4)
    (hgen : relativeMover (d := d) c t ⊔ Z d.radical z ⊔
      Z d.radical (act d.radical x z) = stabilizer d.radical a)
    (hpair : relativeMover (d := d) c t ⊔
      (relativeMover (d := d) c t).map (MulAut.conj x).toMonoidHom = stabilizer d.radical a)
    (hpbad : Z d.radical c ≤ Q d.radical (p.walk.getVert (p.walk.length-2)))
    (hqbad : Z d.radical c ≤ Q d.radical (q.walk.getVert (q.walk.length-2)))
    (hindex : 2 < (B d.radical a ((replacementGeometry h d).Z_normal _)).relIndex
      (U d.radical c)) : False := by
  by_cases hnorm : Z d.radical z ≤ normalizer
      ((Z d.radical c ⊔ Z d.radical a : Subgroup (FreeAmalgam d.radical)) : Set _)
  · have hnormq : ¬ Z d.radical (act d.radical x z) ≤ normalizer
        ((Z d.radical c ⊔ Z d.radical a : Subgroup (FreeAmalgam d.radical)) : Set _) := by
      intro hnormal
      let Y := Z d.radical c ⊔ Z d.radical a
      have hJN : relativeMover (d := d) c t ≤ normalizer (Y : Set (FreeAmalgam d.radical)) :=
        (le_inf ((relativeMover_le_stabilizer (d := d) c t).trans (Z_normalized d.radical c))
          ((hequal.le.trans (relativeMover_le_stabilizer (d := d) a t)).trans (Z_normalized d.radical a))).trans
            (normalizer_inf_normalizer_le_normalizer_sup _ _)
      have hYN : stabilizer d.radical a ≤ normalizer (Y : Set (FreeAmalgam d.radical)) := by
        rw [←hgen]
        exact sup_le (sup_le hJN hnorm) hnormal
      have hYV : Y ≤ V d.radical a :=
        sup_le (neighbor_seed_le_radius hat hct) (Z_le_VBall d.radical a 2)
      let s := fullSymmetricAction_knownSimple h e hz hn d (by omega)
      have hUB : U d.radical c ≤ B d.radical a ((replacementGeometry h d).Z_normal _) :=
        (DistanceEight.U_le_Z d.radical c).trans (le_sup_left.trans
          (SylowSpanSelection.normal_small_radius_le_slice_at s (by omega) p.start_color
            Y hYV hYN (SylowSpanSelection.adjacent_seed_span_index_le_eight
              (e := e) (hz := hz) (hn := hn) hb p.start_color hat hct)))
      have hi := relIndex_eq_one.mpr hUB
      omega
    have hxa : act d.radical x⁻¹ a = a := (stabilizer d.radical a).inv_mem hx
    obtain ⟨r,hr⟩ : ∃ r : CriticalPath d.radical (replacementGeometry h d)
        a (act d.radical x⁻¹ (act d.radical x z)),
        ∀ i, r.walk.getVert i = act d.radical x⁻¹ (q.walk.getVert i) := by
      have hh : ∃ r : CriticalPath d.radical (replacementGeometry h d)
          (act d.radical x⁻¹ a) (act d.radical x⁻¹ (act d.radical x z)),
          ∀ i, r.walk.getVert i = act d.radical x⁻¹ (q.walk.getVert i) :=
        ⟨q.act x⁻¹,fun i => by simp only [CriticalPath.act,actWalk_getVert]⟩
      rwa [hxa] at hh
    have hzx : act d.radical x⁻¹ (act d.radical x z) = z := by
      rw [←act_mul,mul_inv_cancel,act_one]
    have hrs : (Q d.radical (act d.radical x⁻¹ (act d.radical x z))).relIndex
        (Z d.radical a) < 4 := by rwa [hzx]
    have hbad : Z d.radical c ≤ Q d.radical (r.walk.getVert (r.walk.length-2)) := by
      have hrl : r.walk.length = p.walk.length := r.length_eq_b.trans p.length_eq_b.symm
      rw [hrl,hr,hq,←act_mul,mul_inv_cancel,act_one]
      exact hpbad
    have hgen' : relativeMover (d := d) c t ⊔ Z d.radical (act d.radical x z) ⊔
        Z d.radical (act d.radical x⁻¹ (act d.radical x z)) = stabilizer d.radical a := by
      rw [hzx]
      calc
        (relativeMover (d := d) c t ⊔ Z d.radical (act d.radical x z)) ⊔
            Z d.radical z =
            relativeMover (d := d) c t ⊔
              (Z d.radical (act d.radical x z) ⊔ Z d.radical z) := sup_assoc _ _ _
        _ = relativeMover (d := d) c t ⊔
              (Z d.radical z ⊔ Z d.radical (act d.radical x z)) := by
          rw [sup_comm (Z d.radical (act d.radical x z)) (Z d.radical z)]
        _ = (relativeMover (d := d) c t ⊔ Z d.radical z) ⊔
            Z d.radical (act d.radical x z) := (sup_assoc _ _ _).symm
        _ = stabilizer d.radical a := hgen
    have hpair' : relativeMover (d := d) c t ⊔
        (relativeMover (d := d) c t).map (MulAut.conj x⁻¹).toMonoidHom = stabilizer d.radical a := by
      have hh := congrArg (Subgroup.map (MulAut.conj x⁻¹).toMonoidHom) hpair
      have hid : (MulAut.conj x⁻¹).toMonoidHom.comp (MulAut.conj x).toMonoidHom =
          MonoidHom.id (FreeAmalgam d.radical) := by
        apply MonoidHom.ext
        intro y
        simp only [MonoidHom.coe_comp, MulEquiv.coe_toMonoidHom,
          MonoidHom.id_apply]
        change (MulAut.conj (x⁻¹)) ((MulAut.conj x) y) = y
        rw [MulAut.conj_apply, MulAut.conj_apply]
        group
      have hG : (stabilizer d.radical a).map (MulAut.conj x⁻¹).toMonoidHom = stabilizer d.radical a :=
        mem_normalizer_iff_map_conj_eq.mp ((stabilizer d.radical a).le_normalizer
          ((stabilizer d.radical a).inv_mem hx))
      rw [Subgroup.map_sup,map_map,hid,map_id,hG] at hh
      exact (sup_comm _ _).trans hh
    exact paired_traps_impossible_of_nonnormal (e := e) (hz := hz) (hn := hn)
      hb q hqs hat hct hequal x⁻¹ ((stabilizer d.radical a).inv_mem hx)
      r hr hrs hgen' hpair' hqbad hbad hnormq hindex
  · exact paired_traps_impossible_of_nonnormal (e := e) (hz := hz) (hn := hn)
      hb p hsmall hat hct hequal x hx q hq hqs hgen hpair hpbad hqbad hnorm hindex

omit [Finite G] in
/-- Relative movers follow the same graph action as their original edge cores. -/
theorem relativeMover_act (x : FreeAmalgam d.radical) (a t : Vertex d.radical) :
    (relativeMover (d := d) a t).map (MulAut.conj x⁻¹).toMonoidHom =
      relativeMover (d := d) (act d.radical x a) (act d.radical x t) := by
  unfold relativeMover
  rw [SmallMover.join_map _ (MulAut.conj x⁻¹).injective,
    map_inf _ _ _ (MulAut.conj x⁻¹).injective,
    map_normalizer_eq_of_bijective _ (MulAut.conj x⁻¹).bijective,
    ←U_act,←Q_act,←Q_act,←stabilizer_act]

include e hz hn in
/-- A strict equal-relative-mover slice gives an actual paired backward
path. One residual element transports both critical walks; the restricted
original radical is retained as the relative normalizer, of index two over
the actual edge core. No noncentral common-kernel premise is assumed. -/
theorem original_radical_paired_backward_knownSimple
    (hb : 4 < replacementDistance h d)
    {z delta : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) z)
    (hsmall : (Q d.radical z).relIndex (Z d.radical (alpha d.radical)) < 4)
    (hdelta : Adjacent d.radical delta (p.walk.getVert 1))
    (hequal : relativeMover (d := d) delta (p.walk.getVert 1) =
      relativeMover (d := d) (alpha d.radical) (p.walk.getVert 1))
    (hstrict : 2 < (B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _)).relIndex
      (U d.radical delta)) :
    let T := ((R.subgroupOf (L ⊔ R)).subgroupOf d.overgroup).map (embedM d.radical)
    (Q d.radical (beta d.radical)).relIndex T = 2 ∧
      ∃ t, Adjacent d.radical (alpha d.radical) t ∧
        ∃ g ∈ stabilizer d.radical (alpha d.radical),
          act d.radical g (p.walk.getVert 1) = t ∧
          Adjacent d.radical (act d.radical g delta) t ∧
          2 < (B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _)).relIndex
            (U d.radical (act d.radical g delta)) ∧
          ∃ x ∈ Ltilde d.radical (alpha d.radical), x^3 ∈ Q d.radical (alpha d.radical) ∧
            ∃ q : CriticalPath d.radical (replacementGeometry h d)
                (alpha d.radical) (act d.radical x z),
              (∀ i, q.walk.getVert i = act d.radical x (p.walk.getVert i)) ∧
              let c := act d.radical g delta
              let J := relativeMover (d := d) c t
              J = relativeMover (d := d) (alpha d.radical) t ∧
              J ⊔ Z d.radical z ⊔ Z d.radical (act d.radical x z) =
                stabilizer d.radical (alpha d.radical) ∧
              J ⊔ J.map (MulAut.conj x).toMonoidHom = stabilizer d.radical (alpha d.radical) ∧
              (∃ r ∈ stabilizer d.radical (alpha d.radical),
                T.map (MulAut.conj r⁻¹).toMonoidHom =
                  normalizer (Q d.radical t : Set (FreeAmalgam d.radical)) ⊓
                    stabilizer d.radical (alpha d.radical) ∧
                (SmallMover.join (U d.radical (alpha d.radical)) (Q d.radical (alpha d.radical))
                  T 4).map (MulAut.conj r⁻¹).toMonoidHom = J) ∧
              ((∃ b : CriticalPath d.radical (replacementGeometry h d)
                  c (p.walk.getVert (p.walk.length-2)),
                  b.walk.getVert 1 = t ∧
                  ∀ i ≤ p.walk.length-2, b.walk.getVert (i+2) = p.walk.getVert i) ∨
               (∃ b : CriticalPath d.radical (replacementGeometry h d)
                  c (q.walk.getVert (q.walk.length-2)),
                  b.walk.getVert 1 = t ∧
                  ∀ i ≤ q.walk.length-2, b.walk.getVert (i+2) = q.walk.getVert i)) := by
  let T := ((R.subgroupOf (L ⊔ R)).subgroupOf d.overgroup).map (embedM d.radical)
  have hidx : (Q d.radical (beta d.radical)).relIndex T = 2 := by
    rw [Q_beta,relIndex_map_map_of_injective _ _ (embedM_injective d.radical)]
    exact (SylowWholeCore.four_lt_original_sylow_eight_image_knownSimple
      (e := e) (hz := hz) (hn := hn) hb).2.2.1
  obtain ⟨t,hat,x,hxL,hx3,hgen₀,hgen₁,hgen,hpair,hfix⟩ :=
    paired_normalizer_neighbor_knownSimple (e := e) (hz := hz) (hn := hn) hb p hsmall
  have hl : 0 < p.walk.length := p.length_eq_b ▸ replacementDistance_pos h d
  have hfirst : Adjacent d.radical (alpha d.radical) (p.walk.getVert 1) := by
    apply (cosetGraph_adj d.radical _ _).mp
    simpa only [SimpleGraph.Walk.getVert_zero] using p.walk.adj_getVert_succ (i := 0) hl
  obtain ⟨g,hg,hgt⟩ := stabilizer_transitive_neighbors d.radical (alpha d.radical) hfirst hat
  have hct : Adjacent d.radical (act d.radical g delta) t := by
    rw [←hgt]
    exact (adjacent_act_iff d.radical g _ _).mpr hdelta
  have hga : act d.radical g (alpha d.radical) = alpha d.radical := hg
  have heq : relativeMover (d := d) (act d.radical g delta) t =
      relativeMover (d := d) (alpha d.radical) t := by
    have hh := congrArg (Subgroup.map (MulAut.conj g⁻¹).toMonoidHom) hequal
    rwa [relativeMover_act,relativeMover_act,hga,hgt] at hh
  have hB : (B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _)).map
      (MulAut.conj g⁻¹).toMonoidHom = B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _) :=
    mem_normalizer_iff_map_conj_eq.mp (Escape.Propagation.Rigidity.B_normalized
      (by omega : 2 < replacementDistance h d) (alpha d.radical) rfl
      ((stabilizer d.radical (alpha d.radical)).inv_mem hg))
  have hi : 2 < (B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _)).relIndex
      (U d.radical (act d.radical g delta)) := by
    rw [U_act,←hB,relIndex_map_map_of_injective _ _ (MulAut.conj g⁻¹).injective]
    exact hstrict
  have hx : x ∈ stabilizer d.radical (alpha d.radical) := Ltilde_le_stabilizer _ hxL
  have hxa : act d.radical x (alpha d.radical) = alpha d.radical := hx
  obtain ⟨q,hq⟩ : ∃ q : CriticalPath d.radical (replacementGeometry h d)
      (alpha d.radical) (act d.radical x z),
      ∀ i, q.walk.getVert i = act d.radical x (p.walk.getVert i) := by
    have hh : ∃ q : CriticalPath d.radical (replacementGeometry h d)
        (act d.radical x (alpha d.radical)) (act d.radical x z),
        ∀ i, q.walk.getVert i = act d.radical x (p.walk.getVert i) :=
      ⟨p.act x,fun i => by simp only [CriticalPath.act,actWalk_getVert]⟩
    rwa [hxa] at hh
  have hqs : (Q d.radical (act d.radical x z)).relIndex (Z d.radical (alpha d.radical)) < 4 := by
    conv_lhs => rhs; rw [←hxa]
    rw [Q_act,Z_act,relIndex_map_map_of_injective _ _ (MulAut.conj x⁻¹).injective]
    exact hsmall
  change relativeMover (d := d) (alpha d.radical) t ⊔ _ ⊔ _ = _ at hgen
  change relativeMover (d := d) (alpha d.radical) t ⊔
    (relativeMover (d := d) (alpha d.radical) t).map (MulAut.conj x).toMonoidHom = _ at hpair
  rw [←heq] at hgen hpair
  refine ⟨hidx,t,hat,g,hg,hgt,hct,hi,x,hxL,hx3,q,hq,heq,hgen,hpair,?_,?_⟩
  · obtain ⟨r,hr,hrt⟩ := stabilizer_transitive_neighbors d.radical (alpha d.radical)
      (base_adjacent d.radical) hat
    change act d.radical r (beta d.radical) = t at hrt
    have hra : act d.radical r (alpha d.radical) = alpha d.radical := hr
    have hT := SylowSmallNormalizer.four_lt_base_edge_normalizer_knownSimple
      (e := e) (hz := hz) (hn := hn) hb
    have hNm : T.map (MulAut.conj r⁻¹).toMonoidHom =
        normalizer (Q d.radical t : Set (FreeAmalgam d.radical)) ⊓ stabilizer d.radical (alpha d.radical) := by
      rw [show T = _ from hT.symm,map_inf _ _ _ (MulAut.conj r⁻¹).injective,
        map_normalizer_eq_of_bijective _ (MulAut.conj r⁻¹).bijective,
        ←Q_act,←stabilizer_act,hra,hrt]
    refine ⟨r,hr,hNm,?_⟩
    rw [SmallMover.join_map _ (MulAut.conj r⁻¹).injective,←U_act,←Q_act,hra,hNm]
    exact heq.symm
  · let c := act d.radical g delta
    have hcol : color d.radical c = false := by
      have h1 := adjacent_color_ne d.radical hat
      have h2 := adjacent_color_ne d.radical hct
      change false ≠ color d.radical t at h1
      have ht : color d.radical t = true := by
        cases he : color d.radical t
        · exact (h1 he.symm).elim
        · rfl
      cases he : color d.radical c
      · rfl
      · exact (h2 (he.trans ht.symm)).elim
    have backward {v : Vertex d.radical}
        (r : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) v)
        (hbad : ¬ Z d.radical c ≤ Q d.radical (r.walk.getVert (r.walk.length-2))) :
        ∃ b : CriticalPath d.radical (replacementGeometry h d)
            c (r.walk.getVert (r.walk.length-2)),
          b.walk.getVert 1 = t ∧
          ∀ i ≤ r.walk.length-2, b.walk.getVert (i+2) = r.walk.getVert i := by
      let w : (cosetGraph d.radical).Walk c (alpha d.radical) :=
        .cons ((cosetGraph_adj d.radical _ _).mpr hct)
          (.cons ((cosetGraph_adj d.radical _ _).mpr (adjacent_symm d.radical hat)) .nil)
      have hw : w.length = 2 := rfl
      have hb2 : 2 ≤ (replacementGeometry h d).b d.radical := by
        change 2 ≤ replacementDistance h d
        omega
      let b := r.prepend_two hb2 hcol w hw hbad
      refine ⟨b,?_,fun i hi => r.prepend_two_overlap _ _ _ _ _ hi⟩
      change (r.prepend_two _ hcol w hw hbad).walk.getVert 1 = t
      rw [CriticalPath.prepend_two_walk]
      simp only [SimpleGraph.Walk.getVert_append,
        hw,show 1<2 from by decide,ite_true,w,SimpleGraph.Walk.getVert_cons_succ,
        SimpleGraph.Walk.getVert_zero]
    by_cases hpbad : Z d.radical c ≤ Q d.radical (p.walk.getVert (p.walk.length-2))
    · by_cases hqbad : Z d.radical c ≤ Q d.radical (q.walk.getVert (q.walk.length-2))
      · exact (paired_traps_impossible_knownSimple (e := e) (hz := hz) (hn := hn)
          hb p hsmall hat hct heq x hx q hq hqs hgen hpair hpbad hqbad hi).elim
      · exact Or.inr (backward q hqbad)
    · exact Or.inl (backward p hpbad)


include e hz hn in
/-- Trapping bounds every equal-relative-mover slice at the base vertex.
The large critical image is excluded by the existing radius-escape theorem. -/
theorem trapped_equal_mover_slice_base_knownSimple
    (hb : 4 < replacementDistance h d)
    {z c t : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) z)
    (htrap : V d.radical (alpha d.radical) ≤ Q d.radical (p.walk.getVert (p.walk.length-2)))
    (hat : Adjacent d.radical (alpha d.radical) t) (hct : Adjacent d.radical c t)
    (hequal : relativeMover (d := d) c t = relativeMover (d := d) (alpha d.radical) t) :
    (B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _)).relIndex
      (U d.radical c) ≤ 2 := by
  by_contra! hstrict
  have hsmall : (Q d.radical z).relIndex (Z d.radical (alpha d.radical)) < 4 := by
    by_contra! hlarge
    exact SylowActor.four_lt_large_image_radius_escape_knownSimple
      (e := e) (hz := hz) (hn := hn) hb p hlarge htrap
  have hl : 0 < p.walk.length := p.length_eq_b ▸ replacementDistance_pos h d
  have hfirst : Adjacent d.radical (alpha d.radical) (p.walk.getVert 1) := by
    apply (cosetGraph_adj d.radical _ _).mp
    simpa only [SimpleGraph.Walk.getVert_zero] using p.walk.adj_getVert_succ (i := 0) hl
  obtain ⟨j,hj,hjt⟩ := stabilizer_transitive_neighbors d.radical (alpha d.radical) hat hfirst
  have hdelta : Adjacent d.radical (act d.radical j c) (p.walk.getVert 1) := by
    rw [←hjt]
    exact (adjacent_act_iff d.radical j _ _).mpr hct
  have hja : act d.radical j (alpha d.radical) = alpha d.radical := hj
  have hequal' : relativeMover (d := d) (act d.radical j c) (p.walk.getVert 1) =
      relativeMover (d := d) (alpha d.radical) (p.walk.getVert 1) := by
    have hh := congrArg (Subgroup.map (MulAut.conj j⁻¹).toMonoidHom) hequal
    rwa [relativeMover_act,relativeMover_act,hja,hjt] at hh
  have hB : (B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _)).map
      (MulAut.conj j⁻¹).toMonoidHom = B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _) :=
    mem_normalizer_iff_map_conj_eq.mp (Escape.Propagation.Rigidity.B_normalized
      (by omega : 2 < replacementDistance h d) (alpha d.radical) rfl
      ((stabilizer d.radical (alpha d.radical)).inv_mem hj))
  have hi : 2 < (B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _)).relIndex
      (U d.radical (act d.radical j c)) := by
    rw [U_act,←hB,relIndex_map_map_of_injective _ _ (MulAut.conj j⁻¹).injective]
    exact hstrict
  obtain ⟨_,v,hav,g,_,_,hcv,_,x,hx,_,q,hq,_,_,_,_,halt⟩ :=
    original_radical_paired_backward_knownSimple
      (e := e) (hz := hz) (hn := hn) hb p hsmall hdelta hequal' hi
  have hC := neighbor_seed_le_radius hav hcv
  rcases halt with ⟨r,_⟩ | ⟨r,_⟩
  · exact r.critical.2 (hC.trans htrap)
  · have hV : (V d.radical (alpha d.radical)).map (MulAut.conj x⁻¹).toMonoidHom =
        V d.radical (alpha d.radical) :=
      mem_normalizer_iff_map_conj_eq.mp (DistanceEight.V_normalized d.radical _
        ((stabilizer d.radical (alpha d.radical)).inv_mem (Ltilde_le_stabilizer _ hx)))
    have hh := map_mono (f := (MulAut.conj x⁻¹).toMonoidHom) htrap
    rw [hV,←Q_act] at hh
    have hlen : q.walk.length = p.walk.length := q.length_eq_b.trans p.length_eq_b.symm
    apply r.critical.2
    rw [hlen,hq]
    exact hC.trans hh


include e hz hn in
/-- A trapped radius bounds equal-relative-mover slices at every vertex of
its component color, by the literal free-amalgam action. -/
theorem trapped_equal_mover_slice_knownSimple
    (hb : 4 < replacementDistance h d)
    {a z c t : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a z)
    (htrap : V d.radical a ≤ Q d.radical (p.walk.getVert (p.walk.length-2)))
    (hat : Adjacent d.radical a t) (hct : Adjacent d.radical c t)
    (hequal : relativeMover (d := d) c t = relativeMover (d := d) a t) :
    (B d.radical a ((replacementGeometry h d).Z_normal _)).relIndex (U d.radical c) ≤ 2 := by
  obtain ⟨g,hg⟩ := exists_mVertex_of_color d.radical p.start_color
  have hga : act d.radical g⁻¹ a = alpha d.radical := by
    rw [hg,act_mVertex,mul_inv_cancel]
    rfl
  obtain ⟨r,hr⟩ : ∃ r : CriticalPath d.radical (replacementGeometry h d)
      (alpha d.radical) (act d.radical g⁻¹ z),
      ∀ i, r.walk.getVert i = act d.radical g⁻¹ (p.walk.getVert i) := by
    have hh : ∃ r : CriticalPath d.radical (replacementGeometry h d)
        (act d.radical g⁻¹ a) (act d.radical g⁻¹ z),
        ∀ i, r.walk.getVert i = act d.radical g⁻¹ (p.walk.getVert i) :=
      ⟨p.act g⁻¹,fun i => by simp only [CriticalPath.act,actWalk_getVert]⟩
    rwa [hga] at hh
  have hrtrap : V d.radical (alpha d.radical) ≤ Q d.radical (r.walk.getVert (r.walk.length-2)) := by
    have hh := map_mono (f := (MulAut.conj (g⁻¹)⁻¹).toMonoidHom) htrap
    rw [←V_act,←Q_act,hga] at hh
    have hlen : r.walk.length = p.walk.length := r.length_eq_b.trans p.length_eq_b.symm
    rw [hlen,hr]
    exact hh
  have hat' : Adjacent d.radical (alpha d.radical) (act d.radical g⁻¹ t) := by
    rw [←hga]
    exact (adjacent_act_iff d.radical g⁻¹ _ _).mpr hat
  have hequal' : relativeMover (d := d) (act d.radical g⁻¹ c) (act d.radical g⁻¹ t) =
      relativeMover (d := d) (alpha d.radical) (act d.radical g⁻¹ t) := by
    have hh := congrArg (Subgroup.map (MulAut.conj (g⁻¹)⁻¹).toMonoidHom) hequal
    rwa [relativeMover_act,relativeMover_act,hga] at hh
  have hh := trapped_equal_mover_slice_base_knownSimple
    (e := e) (hz := hz) (hn := hn) hb r hrtrap hat'
      ((adjacent_act_iff d.radical g⁻¹ _ _).mpr hct) hequal'
  rw [←hga,Escape.PairingControl.FirstPairing.B_act (by omega : 2 < replacementDistance h d)
    g⁻¹ a p.start_color,U_act,relIndex_map_map_of_injective _ _ (MulAut.conj (g⁻¹)⁻¹).injective] at hh
  exact hh

include e hz hn in
/-- One trapped radius bounds equal-relative-mover slices at every original component
vertex, with no restriction to the trapped path's first edge. -/
theorem trapped_all_equal_slices_le_two_knownSimple
    (hb : 4 < replacementDistance h d)
    {a₀ z : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a₀ z)
    (htrap : V d.radical a₀ ≤ Q d.radical (p.walk.getVert (p.walk.length-2)))
    {a c t : Vertex d.radical} (ha : color d.radical a = false)
    (hat : Adjacent d.radical a t) (hct : Adjacent d.radical c t)
    (hequal : relativeMover (d := d) c t =
      relativeMover (d := d) a t) :
    (B d.radical a ((replacementGeometry h d).Z_normal _)).relIndex (U d.radical c) ≤ 2 := by
  obtain ⟨g,hg⟩ := exists_mVertex_of_color d.radical ha
  obtain ⟨j,hj⟩ := exists_mVertex_of_color d.radical p.start_color
  let y := g⁻¹*j
  have hya : act d.radical y a = a₀ := by
    rw [hg,hj,act_mVertex]
    simp only [y,mul_inv_cancel_left]
  have hyt : Adjacent d.radical a₀ (act d.radical y t) := by
    rw [←hya]
    exact (adjacent_act_iff d.radical y _ _).mpr hat
  have hequal' : relativeMover (d := d) (act d.radical y c) (act d.radical y t) =
      relativeMover (d := d) a₀ (act d.radical y t) := by
    have hh := congrArg (Subgroup.map (MulAut.conj y⁻¹).toMonoidHom) hequal
    rwa [relativeMover_act,relativeMover_act,hya] at hh
  have hh := trapped_equal_mover_slice_knownSimple
    (e := e) (hz := hz) (hn := hn) hb p htrap hyt
      ((adjacent_act_iff d.radical y _ _).mpr hct) hequal'
  rw [←hya,Escape.PairingControl.FirstPairing.B_act (by omega : 2 < replacementDistance h d)
    y a ha,U_act,relIndex_map_map_of_injective _ _ (MulAut.conj y⁻¹).injective] at hh
  exact hh

include e hz hn in
/-- On an equal-relative-mover last edge, trapping identifies the actual full reverse
kernel with the predecessor slice and forces both critical indices to two. -/
theorem trapped_equal_predecessor_kernel_knownSimple
    (hb : 4 < replacementDistance h d)
    {a₀ z : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a₀ z)
    (htrap : V d.radical a₀ ≤ Q d.radical (p.walk.getVert (p.walk.length-2)))
    {a a' : Vertex d.radical}
    (q : CriticalPath d.radical (replacementGeometry h d) a a')
    (hequal : relativeMover (d := d) a' (q.walk.getVert (q.walk.length-1)) =
      relativeMover (d := d) (q.walk.getVert (q.walk.length-2))
        (q.walk.getVert (q.walk.length-1))) :
    Z d.radical a' ⊓ B d.radical (q.walk.getVert (q.walk.length-2))
        ((replacementGeometry h d).Z_normal _) = Z d.radical a' ⊓ Q d.radical a ∧
      (Q d.radical a').relIndex (Z d.radical a) = 2 ∧
      (Q d.radical a).relIndex (Z d.radical a') = 2 := by
  have hb2 : 2 < replacementDistance h d := by omega
  let s := fullSymmetricAction_knownSimple h e hz hn d hb2
  have hc := DistanceTwo.centralLayer_knownSimple G L R h e hz hn d
  have hl : 2 < q.walk.length := q.length_eq_b ▸ hb2
  have hcol : color d.radical (q.walk.getVert (q.walk.length-2)) = false := by
    apply (q.vertex_color (Nat.sub_le _ _)).mpr
    have he := replacementDistance_even h d
    rw [Nat.even_iff] at he ⊢
    have hh : q.walk.length = replacementDistance h d := q.length_eq_b
    omega
  have hct : Adjacent d.radical (q.walk.getVert (q.walk.length-2))
      (q.walk.getVert (q.walk.length-1)) := by
    have hh := q.walk.adj_getVert_succ (i := q.walk.length-2) (by omega)
    rw [show q.walk.length-2+1=q.walk.length-1 by omega] at hh
    exact (cosetGraph_adj d.radical _ _).mp hh
  have het : Adjacent d.radical a' (q.walk.getVert (q.walk.length-1)) := by
    have hh := q.walk.adj_getVert_succ (i := q.walk.length-1) (by omega)
    rw [show q.walk.length-1+1=q.walk.length by omega,q.walk.getVert_length] at hh
    exact adjacent_symm d.radical ((cosetGraph_adj d.radical _ _).mp hh)
  exact critical_predecessor_slice_eq_kernel s hc hb2 q
    (trapped_all_equal_slices_le_two_knownSimple (e := e) (hz := hz) (hn := hn)
      hb p htrap hcol hct het hequal)

end AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.EightPairedNormalizer
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
