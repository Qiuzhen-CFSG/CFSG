module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.Terminal.ElementarySmallIntersection
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.Terminal.ElementarySmallKernel
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.Terminal.SmallKernelOppositeSlice

/-!
# Distinct paired kernels in the strict cube branch

At distance four, a strict forward Baumann slice and a small opposite slice
select two compatible backward critical paths. A trapped second candidate
would have zero reverse-kernel movement: its commutator lies in the compatible
triple intersection and in the small opposite residual fixer, so centrality
transports to its full seed. The full-cover central-commutator theorem then
forces that commutator to vanish.

Both candidates are therefore critical. Their own full backward-kernel joins
are normalized by their corresponding endpoint actors. The strict-slice
obstruction shows that these kernels are distinct; hence the joint endpoint
image at the backward vertex has order greater than two. The proof uses both
full moving covers and retains all central attachments.

This establishes the distinct-kernel step of Meierfrankenfeld--Stellmacher,
*Pushing up weak BN-pairs of rank two* (1993), (5.12)(3), printed p.927.
The deeper common-kernel generation and terminal contradiction remain separate.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation BinaryPermutation
open scoped commutatorElement IsMulCommutative Pointwise
open CFSG.Quasithin.ChapterB.Offenders CFSG.Quasithin.ChapterB.Offenders.Six
open Theory.SpecificGroups.SymmetricSix
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.Terminal
universe u
variable {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
  {h : SmallMSPair KnownSimple.IsKnownSimple L R} {e : CentralMarking L}
  {hz : center (L ⧸ pCore 2 L) = ⊥} {hn : InitialNatural h e hz}
  {d : Replacement L R}

private theorem seed_central_commutator_eq_bot
    (s : FullSymmetricAction h e hz hn d) (hc : DistanceTwo.CentralLayer d)
    {c : Vertex d.radical} (hcol : color d.radical c = false)
    (F : Subgroup (FreeAmalgam d.radical))
    (hFG : F ≤ stabilizer d.radical c)
    (hcentral : ⁅Z d.radical c,F⁆ ≤ centralizer (stabilizer d.radical c : Set _)) :
    ⁅Z d.radical c,F⁆ = ⊥ := by
  obtain ⟨i,hi,hir,hiQ,hiU⟩ := vertex_coordinates (h := h) hc c hcol
  let A := F.comap i
  have hmA : A.map i = F := map_comap_eq_self (hFG.trans_eq hir.symm)
  have hcA : ⁅replacementMoved d,A⁆ ≤ center d.overgroup := by
    intro x hx
    apply mem_center_iff.mpr
    intro m
    apply hi
    simp only [map_mul]
    apply hcentral
    · have hh := mem_map_of_mem i hx
      rw [map_commutator,hmA,hiU] at hh
      exact (commutator_mono (DistanceEight.U_le_Z d.radical c) le_rfl) hh
    · rw [←hir]
      exact ⟨m,rfl⟩
  have hFQ := map_mono (f := i) (cover_central_commutator_forces_core s A hcA)
  rw [hmA,hiQ] at hFQ
  exact le_antisymm ((commutator_mono le_rfl hFQ).trans
    (Z_centralizes_Q d.radical c hcol).le) bot_le

/-- A trapped backward seed has no reverse-kernel movement when the opposite
slice is small and the compatible triple is central. Thus the endpoint acts
trivially on its full join modulo the starting seed. -/
theorem cube_trapped_opposite_actor_movement
    (s : FullSymmetricAction h e hz hn d) (hc : DistanceTwo.CentralLayer d)
    (hb : replacementDistance h d = 4)
    (u : Equiv.Perm (Fin 6))
    (hfull : d.radical.map s.projection = (D 6).map (MulAut.conj u).toMonoidHom)
    {a z c t : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a z)
    (hsmall : (Q d.radical z).relIndex (Z d.radical a) < 4)
    (hat : Adjacent d.radical a t) (hct : Adjacent d.radical c t)
    (htrapped : Z d.radical c ≤ Q d.radical (p.walk.getVert 2))
    (g : FreeAmalgam d.radical) (hg : g ∈ stabilizer d.radical a)
    (hgc : act d.radical g (p.walk.getVert 2) = c)
    (hopposite : (B d.radical (p.walk.getVert 2)
      ((replacementGeometry h d).Z_normal _)).relIndex (U d.radical z) ≤ 2)
    (hbackward : Z d.radical c ⊓ Z d.radical a ⊓ Z d.radical (p.walk.getVert 2) ≤
      centralizer (stabilizer d.radical a : Set (FreeAmalgam d.radical))) :
    ⁅Z d.radical c,Z d.radical z⁆ ≤ Z d.radical a := by
  have hb2 : 2 < replacementDistance h d := by omega
  have hl : p.walk.length = 4 := p.length_eq_b.trans hb
  let v := p.walk.getVert 2
  let F := Z d.radical z ⊓ Q d.radical a
  let H := ⁅Z d.radical c,F⁆
  have ht : color d.radical t = true := by
    have hh := adjacent_color_ne d.radical hat
    rw [p.start_color] at hh
    exact Bool.eq_true_of_not_eq_false (Ne.symm hh)
  have hcol : color d.radical c = false := by
    have hh := adjacent_color_ne d.radical hct
    rw [ht] at hh
    cases he : color d.radical c <;> simp_all
  have hFG : F ≤ stabilizer d.radical c :=
    (inf_le_right.trans (Q_le_adjacent_h d.radical ht hat)).trans
      (fun _ hx => hx.2 _ (adjacent_symm d.radical hct))
  have hHc : H ≤ Z d.radical c :=
    le_normalizer_iff_commutator_le_left.mp (hFG.trans (Z_normalized d.radical c))
  have hHseeds := (cube_backward_kernel_le_edge_seeds s hc hb2 u hfull.le p hat hct
    (by simpa only [hl] using htrapped)).2
  change H ≤ Z d.radical a ⊓ Z d.radical (p.walk.getVert (p.walk.length-2)) at hHseeds
  simp only [hl] at hHseeds
  have hcenta := (le_inf (le_inf hHc (hHseeds.trans inf_le_left))
    (hHseeds.trans inf_le_right)).trans hbackward
  have hv : color d.radical v = false := (p.vertex_color (by omega)).mpr (by decide)
  have hHX : H ≤ X d.radical v := (hHseeds.trans inf_le_right).trans
    ((replacementGeometry h d).omega_bound v hv (by
      rw [(replacementGeometry h d).distance_constant v hv]
      exact replacementDistance_pos h d))
  have hHfixed : H ≤ fixedCore d.radical v := by
    rw [show H = ⁅F,Z d.radical c⁆ from commutator_comm _ _]
    exact (commutator_mono le_rfl htrapped).trans
      (small_predecessor_whole_core_fixed s hc hb p hopposite)
  have hcentv := (le_inf hHX hHfixed).trans
    (omega_fixed_central_of_small_critical s hc p hsmall v hv)
  have hcentc : H ≤ centralizer (stabilizer d.radical c : Set (FreeAmalgam d.radical)) := by
    rw [←hgc,stabilizer_act]
    have hh := (map_mono (f := (MulAut.conj g⁻¹).toMonoidHom) hcentv).trans
      (map_centralizer_le_centralizer_image _ _)
    have hf : H.map (MulAut.conj g⁻¹).toMonoidHom = H :=
      mem_normalizer_iff_map_conj_eq.mp (Subgroup.centralizer_le_normalizer _
        (le_centralizer_iff.mp hcenta ((stabilizer d.radical a).inv_mem hg)))
    rwa [hf] at hh
  have hzero : H = ⊥ := seed_central_commutator_eq_bot s hc hcol F hFG hcentc
  exact small_critical_predecessor_commutator s hc hb2 p hsmall (Z d.radical c)
    (by simpa only [hl] using htrapped) (commutator_eq_bot_iff_le_centralizer.mp hzero)

include e hz hn in
/-- On the actual strict cube shift, a small opposite slice normalizes the
full backward kernel under the original endpoint. Its cubic partner must
fail to normalize that same join. -/
theorem cube_strict_small_opposite_paired_obstruction_knownSimple
    (hb : replacementDistance h d = 4)
    (u : Equiv.Perm (Fin 6))
    (him : d.radical.map (SourceReduction.projection h e hz hn d) =
      (D 6).map (MulAut.conj u).toMonoidHom)
    {a z : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a z)
    (hstrict : 2 < (B d.radical a ((replacementGeometry h d).Z_normal _)).relIndex
      (U d.radical (p.walk.getVert 2)))
    (hopposite : (B d.radical (p.walk.getVert 2)
      ((replacementGeometry h d).Z_normal _)).relIndex (U d.radical z) ≤ 2) :
    ∃ q : EdgePairedBackwardShift (h := h) p,
      2 < (B d.radical a ((replacementGeometry h d).Z_normal _)).relIndex
        (U d.radical q.start) ∧
      q.cubic ∈ normalizer (Q d.radical (p.walk.getVert 1) : Set (FreeAmalgam d.radical)) ∧
      let J := (Z d.radical q.start ⊓ Q d.radical (p.walk.getVert 2)) ⊔ Z d.radical a
      Z d.radical z ≤ normalizer (J : Set (FreeAmalgam d.radical)) ∧
      ¬ Z d.radical (act d.radical q.cubic z) ≤ normalizer (J : Set (FreeAmalgam d.radical)) := by
  have hb2 : 2 < replacementDistance h d := by omega
  let s := fullSymmetricAction_knownSimple h e hz hn d hb2
  have hc := DistanceTwo.centralLayer_knownSimple G L R h e hz hn d
  have hfull : d.radical.map s.projection = (D 6).map (MulAut.conj u).toMonoidHom := by
    rwa [SourceReduction.fullSymmetricAction_projection_unique h e hz hn d s]
  have hel : IsElementaryAbelian 2 (d.radical.map s.projection) := by
    let : IsElementaryAbelian 2 (D 6) := elementary_disjointTranspositions (3 : Fin 4)
    rw [hfull]
    exact IsElementaryAbelian.map _
  obtain ⟨q,hq,hx,htriple⟩ := cube_strict_backward_triple_at_knownSimple
    (e := e) (hz := hz) (hn := hn) hb u him p hstrict
  have hl : p.walk.length = 4 := p.length_eq_b.trans hb
  obtain ⟨r,hr2,hr1⟩ : ∃ r : CriticalPath d.radical (replacementGeometry h d)
      q.start (p.walk.getVert 2), r.walk.getVert 2 = a ∧ r.walk.getVert 1 = q.edge := by
    have hh : ∃ r : CriticalPath d.radical (replacementGeometry h d)
        q.start (p.walk.getVert (p.walk.length-2)),
        r.walk.getVert 2 = a ∧ r.walk.getVert 1 = q.edge := by
      refine ⟨q.path,?_,q.first⟩
      simpa only [Nat.zero_add,SimpleGraph.Walk.getVert_zero] using q.overlap 0 (by omega)
    rw [show p.walk.length-2=2 by omega] at hh
    exact hh
  have hZV : Z d.radical q.start ≤ V d.radical a :=
    (Z_le_localZSpan d.radical _ _).trans (localZSpan_le_V d.radical (by
      have hh := r.dist_start (i := 2) (by have hrl := r.length_eq_b.trans hb; omega)
      rw [hr2] at hh
      exact hh.le))
  have hmove : ⁅Z d.radical q.start,Q d.radical a⁆ ≤ Z d.radical a :=
    (commutator_mono hZV le_rfl).trans
      (cube_radius_core_commutator_le_seed s hc hb2 u hfull.le a p.start_color)
  have hsmall := critical_image_small_at_knownSimple (e := e) (hz := hz) (hn := hn) hb p
  have hrsmall := critical_image_small_at_knownSimple (e := e) (hz := hz) (hn := hn) hb r
  have hnorm := small_backward_kernel_normalized_of_opposite_slice s hc hb p hsmall r hr2
    hrsmall hmove q.transporter q.transporter_mem q.start_eq hopposite htriple
  refine ⟨q,hq,hx,hnorm,?_⟩
  intro hother
  have hgen : Ltilde d.radical (r.walk.getVert 2) ≤ Q d.radical (r.walk.getVert 1) ⊔
      (Z d.radical z ⊔ Z d.radical (act d.radical q.cubic z)) := by
    rw [hr1,hr2,←sup_assoc,q.endpoint_generation]
    exact Ltilde_le_stabilizer _
  have hbound := elementary_small_normalized_slice_le_two s hc hb hel r hrsmall
    (Z d.radical z ⊔ Z d.radical (act d.radical q.cubic z)) hgen
    (by simpa only [hr2] using sup_le hnorm hother)
  exact (not_le_of_gt hq) (by simpa only [hr2] using hbound)

private theorem small_distinct_kernels_joint_image_gt_two
    (s : FullSymmetricAction h e hz hn d) (hc : DistanceTwo.CentralLayer d)
    {c v w : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) c v)
    (q : CriticalPath d.radical (replacementGeometry h d) c w)
    (hp : (Q d.radical v).relIndex (Z d.radical c) < 4)
    (hq : (Q d.radical w).relIndex (Z d.radical c) < 4)
    (hne : Z d.radical c ⊓ Q d.radical v ≠ Z d.radical c ⊓ Q d.radical w) :
    2 < (Q d.radical c).relIndex (Z d.radical v ⊔ Z d.radical w) := by
  by_contra! hbound
  have hAG (z : Vertex d.radical)
      (r : CriticalPath d.radical (replacementGeometry h d) c z) :
      Z d.radical z ≤ stabilizer d.radical c :=
    critical_Z_le_stabilizer d.radical (replacementGeometry h d) c p.start_color
      (by rw [(replacementGeometry h d).distance_constant c p.start_color]
          exact replacementDistance_pos h d) r.critical
  obtain ⟨i,hi,hir,hiQ,hiU⟩ := vertex_coordinates (h := h) hc c p.start_color
  have imageCard (A : Subgroup (FreeAmalgam d.radical)) (hA : A ≤ stabilizer d.radical c) :
      Nat.card ((A.comap i).map s.projection) = (Q d.radical c).relIndex A := by
    rw [←relIndex_ker,s.projection_kernel]
    have hh := relIndex_map_map_of_injective (pCore 2 d.overgroup) (A.comap i) hi
    rw [hiQ,map_comap_eq_self (hA.trans_eq hir.symm)] at hh
    exact hh.symm
  let E := Z d.radical v ⊔ Z d.radical w
  have hEG : E ≤ stabilizer d.radical c := sup_le (hAG v p) (hAG w q)
  have hEcard : Nat.card ((E.comap i).map s.projection) ≤ 2 := by
    rwa [imageCard E hEG]
  have him0 : ((Z d.radical v).comap i).map s.projection = (E.comap i).map s.projection :=
    eq_of_le_of_card_ge (map_mono (comap_mono le_sup_left)) (by
      rw [imageCard _ (hAG v p),(small_critical_indices s hc p hp).2]
      exact hEcard)
  have him1 : ((Z d.radical w).comap i).map s.projection = (E.comap i).map s.projection :=
    eq_of_le_of_card_ge (map_mono (comap_mono le_sup_right)) (by
      rw [imageCard _ (hAG w q),(small_critical_indices s hc q hq).2]
      exact hEcard)
  have hjoin : Z d.radical v ⊔ Q d.radical c = Z d.radical w ⊔ Q d.radical c := by
    have hh := congrArg (Subgroup.comap s.projection) (him0.trans him1.symm)
    rw [comap_map_eq,comap_map_eq,s.projection_kernel] at hh
    have hh' := congrArg (Subgroup.map i) hh
    simpa only [Subgroup.map_sup,hiQ,map_comap_eq_self ((hAG v p).trans_eq hir.symm),
      map_comap_eq_self ((hAG w q).trans_eq hir.symm)] using hh'
  have hQC : Q d.radical c ≤ centralizer (Z d.radical c : Set (FreeAmalgam d.radical)) :=
    le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp
      (Z_centralizes_Q d.radical c p.start_color))
  have fixed_join (A : Subgroup (FreeAmalgam d.radical)) :
      Z d.radical c ⊓ centralizer ((A ⊔ Q d.radical c : Subgroup (FreeAmalgam d.radical)) : Set _) =
        Z d.radical c ⊓ centralizer (A : Set _) := by
    apply le_antisymm
    · intro x hx
      exact ⟨hx.1, fun y hy => hx.2 y (mem_sup_left hy)⟩
    refine le_inf inf_le_left (le_centralizer_iff.mpr (sup_le ?_ ?_))
    · exact le_centralizer_iff.mp inf_le_right
    · exact hQC.trans (centralizer_le inf_le_left)
  have kernel (z : Vertex d.radical)
      (r : CriticalPath d.radical (replacementGeometry h d) c z) :
      Z d.radical c ⊓ Q d.radical z = Z d.radical c ⊓ centralizer (Z d.radical z : Set _) := by
    rw [←C_eq_Q s hc z r.end_color]
    apply le_antisymm (inf_le_inf_left _ inf_le_right)
    apply le_inf inf_le_left
    apply le_inf ?_ inf_le_right
    exact inf_le_left.trans (critical_Z_le_stabilizer d.radical (replacementGeometry h d)
      z r.end_color (by
        rw [(replacementGeometry h d).distance_constant z r.end_color]
        exact replacementDistance_pos h d) (critical_reverse_pair s hc r))
  apply hne
  rw [kernel v p,kernel w q,←fixed_join (Z d.radical v),←fixed_join (Z d.radical w),hjoin]


include e hz hn in
/-- In the strict-forward, small-opposite case both cubic backward candidates
are critical, and their full kernels at the selected seed are distinct. -/
theorem cube_strict_small_opposite_distinct_kernels_knownSimple
    (hb : replacementDistance h d = 4)
    (u : Equiv.Perm (Fin 6))
    (him : d.radical.map (SourceReduction.projection h e hz hn d) =
      (D 6).map (MulAut.conj u).toMonoidHom)
    {a z : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a z)
    (hstrict : 2 < (B d.radical a ((replacementGeometry h d).Z_normal _)).relIndex
      (U d.radical (p.walk.getVert 2)))
    (hopposite : (B d.radical (p.walk.getVert 2)
      ((replacementGeometry h d).Z_normal _)).relIndex (U d.radical z) ≤ 2) :
    ∃ q : EdgePairedBackwardShift (h := h) p,
      2 < (B d.radical a ((replacementGeometry h d).Z_normal _)).relIndex
        (U d.radical q.start) ∧
      q.cubic ∈ normalizer (Q d.radical (p.walk.getVert 1) : Set (FreeAmalgam d.radical)) ∧
      ∃ r : CriticalPath d.radical (replacementGeometry h d) q.start
          (act d.radical q.cubic (p.walk.getVert 2)),
        r.walk.getVert 1 = q.edge ∧ r.walk.getVert 2 = a ∧
        Z d.radical q.start ⊓ Q d.radical (p.walk.getVert 2) ≠
          Z d.radical q.start ⊓ Q d.radical (act d.radical q.cubic (p.walk.getVert 2)) ∧
        2 < (Q d.radical q.start).relIndex
          (Z d.radical (p.walk.getVert 2) ⊔
            Z d.radical (act d.radical q.cubic (p.walk.getVert 2))) := by
  have hb2 : 2 < replacementDistance h d := by omega
  let s := fullSymmetricAction_knownSimple h e hz hn d hb2
  have hc := DistanceTwo.centralLayer_knownSimple G L R h e hz hn d
  have hfull : d.radical.map s.projection = (D 6).map (MulAut.conj u).toMonoidHom := by
    rwa [SourceReduction.fullSymmetricAction_projection_unique h e hz hn d s]
  obtain ⟨q,hq,hxN,hnorm,hbad⟩ := cube_strict_small_opposite_paired_obstruction_knownSimple
    (e := e) (hz := hz) (hn := hn) hb u him p hstrict hopposite
  let x := q.cubic
  have hxG : x ∈ stabilizer d.radical a := Ltilde_le_stabilizer _ q.cubic_mem
  have hxa : act d.radical x a = a := hxG
  have hl : p.walk.length = 4 := p.length_eq_b.trans hb
  obtain ⟨w,hw⟩ : ∃ w : CriticalPath d.radical (replacementGeometry h d)
      a (act d.radical x z), ∀ i, w.walk.getVert i = act d.radical x (p.walk.getVert i) := by
    have hh : ∃ w : CriticalPath d.radical (replacementGeometry h d)
        (act d.radical x a) (act d.radical x z),
        ∀ i, w.walk.getVert i = act d.radical x (p.walk.getVert i) :=
      ⟨p.act x,fun i => by simp only [CriticalPath.act,actWalk_getVert]⟩
    rwa [hxa] at hh
  have hwl : w.walk.length = 4 := w.length_eq_b.trans hb
  have hv : color d.radical (p.walk.getVert 2) = false :=
    (p.vertex_color (by omega)).mpr (by decide)
  have hstrictx : 2 < (B d.radical a ((replacementGeometry h d).Z_normal _)).relIndex
      (U d.radical (w.walk.getVert 2)) := by
    rw [hw]
    have hB := Escape.PairingControl.FirstPairing.B_act
      (geometry := replacementGeometry h d) hb2 x a p.start_color
    rw [hxa] at hB
    rw [hB,U_act,relIndex_map_map_of_injective _ _ (MulAut.conj x⁻¹).injective]
    exact hstrict
  have hoppositex : (B d.radical (w.walk.getVert 2)
      ((replacementGeometry h d).Z_normal _)).relIndex (U d.radical (act d.radical x z)) ≤ 2 := by
    rw [hw,Escape.PairingControl.FirstPairing.B_act hb2 x (p.walk.getVert 2) hv,
      U_act,relIndex_map_map_of_injective _ _ (MulAut.conj x⁻¹).injective]
    exact hopposite
  have hwa1 : Adjacent d.radical a (w.walk.getVert 1) := by
    apply (cosetGraph_adj d.radical _ _).mp
    simpa only [SimpleGraph.Walk.getVert_zero] using w.walk.adj_getVert_succ (i := 0) (by omega)
  have hw21 : Adjacent d.radical (w.walk.getVert 2) (w.walk.getVert 1) :=
    adjacent_symm d.radical ((cosetGraph_adj d.radical _ _).mp
      (w.walk.adj_getVert_succ (i := 1) (by omega)))
  have hQfirst : Q d.radical (w.walk.getVert 1) = Q d.radical (p.walk.getVert 1) := by
    rw [hw,Q_act]
    exact mem_normalizer_iff_map_conj_eq.mp
      ((normalizer (Q d.radical (p.walk.getVert 1) : Set (FreeAmalgam d.radical))).inv_mem hxN)
  have htriplex : Z d.radical q.start ⊓ Z d.radical a ⊓ Z d.radical (w.walk.getVert 2) ≤
      centralizer (stabilizer d.radical a : Set (FreeAmalgam d.radical)) := by
    have hh := cube_strict_compatible_triple_central s hb2 u hfull p.start_color
      hwa1 hw21 q.adjacent_start q.adjacent_shift hstrictx hq
      (by rw [hQfirst]; exact q.first_kernel_generation)
    have he : Z d.radical q.start ⊓ Z d.radical a ⊓ Z d.radical (w.walk.getVert 2) =
        Z d.radical (w.walk.getVert 2) ⊓ Z d.radical a ⊓ Z d.radical q.start := by ac_rfl
    rwa [he]
  let j := x⁻¹*q.transporter
  have hj : j ∈ stabilizer d.radical a := mul_mem (inv_mem hxG) q.transporter_mem
  have hjc : act d.radical j (w.walk.getVert 2) = q.start := by
    have hcancel (v : Vertex d.radical) : act d.radical x⁻¹ (act d.radical x v) = v := by
      rw [←act_mul,mul_inv_cancel,act_one]
    rw [hw,show j=x⁻¹*q.transporter from rfl,act_mul,hcancel]
    exact q.start_eq
  have hsmall := critical_image_small_at_knownSimple (e := e) (hz := hz) (hn := hn) hb w
  have hca : (cosetGraph d.radical).dist q.start a ≤ 2 := by
    have h1 := SimpleGraph.dist_eq_one_iff_adj.mpr
      ((cosetGraph_adj d.radical _ _).mpr q.adjacent_shift)
    have h2 := SimpleGraph.dist_eq_one_iff_adj.mpr
      ((cosetGraph_adj d.radical _ _).mpr (adjacent_symm d.radical q.adjacent_start))
    simpa only [h1,h2] using (cosetGraph_connected d.radical).dist_triangle
      (u := q.start) (v := q.edge) (w := a)
  have hZV : Z d.radical q.start ≤ V d.radical a :=
    (Z_le_localZSpan d.radical _ _).trans (localZSpan_le_V d.radical hca)
  have hmove : ⁅Z d.radical q.start,Q d.radical a⁆ ≤ Z d.radical a :=
    (commutator_mono hZV le_rfl).trans
      (cube_radius_core_commutator_le_seed s hc hb2 u hfull.le a p.start_color)
  have hescape : ¬ Z d.radical q.start ≤ Q d.radical (w.walk.getVert 2) := by
    intro htrap
    have hwhole := cube_trapped_opposite_actor_movement s hc hb u hfull w hsmall
      q.adjacent_start q.adjacent_shift htrap j hj hjc hoppositex htriplex
    apply hbad
    apply le_normalizer_iff_commutator_le_left.mpr
    apply le_trans ?_ le_sup_right
    apply commutator_sup_le_of_relative_normal (stabilizer d.radical a)
      _ (Z d.radical a) (Z d.radical (act d.radical x z)) (Z d.radical a)
      (Z_normalized d.radical a)
      (inf_le_left.trans (hZV.trans (((replacementGeometry h d).V_le_Q hb2 a p.start_color).trans
        (fun _ hx => hx.1))))
      (Z_le_stabilizer d.radical a)
    · exact (commutator_mono inf_le_left le_rfl).trans hwhole
    · exact le_normalizer_iff_commutator_le_left.mp
        ((critical_Z_le_stabilizer d.radical (replacementGeometry h d) a p.start_color
          (by rw [(replacementGeometry h d).distance_constant a p.start_color]
              exact replacementDistance_pos h d) w.critical).trans (Z_normalized d.radical a))
  obtain ⟨r,hr1,hr2⟩ : ∃ r : CriticalPath d.radical (replacementGeometry h d) q.start
      (act d.radical x (p.walk.getVert 2)),
      r.walk.getVert 1 = q.edge ∧ r.walk.getVert 2 = a := by
    let path : (cosetGraph d.radical).Walk q.start a :=
      .cons ((cosetGraph_adj d.radical _ _).mpr q.adjacent_shift)
        (.cons ((cosetGraph_adj d.radical _ _).mpr (adjacent_symm d.radical q.adjacent_start)) .nil)
    have hpath : path.length = 2 := rfl
    have hcol : color d.radical q.start = false := q.path.start_color
    let r := w.prepend_two (Nat.le_of_lt hb2) hcol path hpath (by simpa only [hwl] using hescape)
    have hh : ∃ r : CriticalPath d.radical (replacementGeometry h d) q.start
        (w.walk.getVert (w.walk.length-2)), r.walk.getVert 1 = q.edge ∧ r.walk.getVert 2 = a := by
      refine ⟨r,?_,?_⟩
      · simp only [r,CriticalPath.prepend_two_walk,SimpleGraph.Walk.getVert_append,
          hpath,show 1<2 from by decide,ite_true,path,SimpleGraph.Walk.getVert_cons_succ,
          SimpleGraph.Walk.getVert_zero]
      · simpa only [Nat.zero_add,SimpleGraph.Walk.getVert_zero] using
          w.prepend_two_overlap (Nat.le_of_lt hb2) hcol path hpath
            (by simpa only [hwl] using hescape) (i := 0) (by omega)
    rw [show w.walk.length-2=2 by omega,hw] at hh
    exact hh
  have hnormx : Z d.radical (act d.radical x z) ≤ normalizer
      (((Z d.radical q.start ⊓ Q d.radical (act d.radical x (p.walk.getVert 2))) ⊔
        Z d.radical a : Subgroup (FreeAmalgam d.radical)) : Set _) := by
    have hh : ∀ r : CriticalPath d.radical (replacementGeometry h d) q.start
        (w.walk.getVert 2), r.walk.getVert 2 = a → Z d.radical (act d.radical x z) ≤ normalizer
        (((Z d.radical q.start ⊓ Q d.radical (w.walk.getVert 2)) ⊔ Z d.radical a :
          Subgroup (FreeAmalgam d.radical)) : Set _) := by
      intro r hr
      exact small_backward_kernel_normalized_of_opposite_slice s hc hb w hsmall r hr
        (critical_image_small_at_knownSimple (e := e) (hz := hz) (hn := hn) hb r)
        hmove j hj hjc hoppositex htriplex
    rw [hw] at hh
    exact hh r hr2
  have hne : Z d.radical q.start ⊓ Q d.radical (p.walk.getVert 2) ≠
      Z d.radical q.start ⊓ Q d.radical (act d.radical x (p.walk.getVert 2)) := by
    intro he
    exact hbad (he ▸ hnormx)
  refine ⟨q,hq,hxN,r,hr1,hr2,hne,?_⟩
  have hp' : ∃ p' : CriticalPath d.radical (replacementGeometry h d) q.start
      (p.walk.getVert 2), True := by
    have hh := q.path
    rw [show p.walk.length - 2 = 2 by omega] at hh
    exact ⟨hh,trivial⟩
  obtain ⟨p',_⟩ := hp'
  exact small_distinct_kernels_joint_image_gt_two s hc p' r
    (critical_image_small_at_knownSimple (e := e) (hz := hz) (hn := hn) hb p')
    (critical_image_small_at_knownSimple (e := e) (hz := hz) (hn := hn) hb r) hne

end AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.Terminal
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
