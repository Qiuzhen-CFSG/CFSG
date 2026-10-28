module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.Terminal.ElementarySmallOppositeExclusion
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.Terminal.SmallKernelNormalizationCompatible
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.Terminal.ElementarySmallOpposite

/-!
# A central forward triple excludes a strict cube slice

A central forward seed triple replaces the small opposite-slice hypothesis
in the paired-kernel argument. It fixes the failure line at the forward
midpoint and transports that fixedness through the compatible backward
selection. The two cubic backward candidates are critical with distinct
full kernels. Their paired generation then feeds the second backward
contradiction, retaining both moving covers and all central attachments.

Source: Meierfrankenfeld--Stellmacher (1993), (5.12)(1),(3), pp.924--927.
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
local notation "S" => Equiv.Perm (Fin 6)
universe u
variable {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
  {h : SmallMSPair KnownSimple.IsKnownSimple L R} {e : CentralMarking L}
  {hz : center (L ⧸ pCore 2 L) = ⊥} {hn : InitialNatural h e hz}
  {d : Replacement L R}

/-- A trapped backward seed has no reverse-kernel movement when both the
forward and compatible backward triples are central. Thus the endpoint acts
trivially on its full join modulo the starting seed. -/
theorem cube_trapped_forward_triple_actor_movement
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
    (hforward : Z d.radical a ⊓ Z d.radical (p.walk.getVert 2) ⊓ Z d.radical z ≤
      centralizer (stabilizer d.radical (p.walk.getVert 2) : Set (FreeAmalgam d.radical)))
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
  have hlastAdj : Adjacent d.radical z (p.walk.getVert (p.walk.length-1)) := by
    have hh := p.walk.adj_getVert_succ (i := p.walk.length-1) (by omega)
    rw [show p.walk.length-1+1=p.walk.length by omega,p.walk.getVert_length] at hh
    exact adjacent_symm d.radical ((cosetGraph_adj d.radical _ _).mp hh)
  have hHz : H ≤ Z d.radical z :=
    ((cube_backward_kernel_le_edge_seeds s hc hb2 u hfull.le p hat hct
      (by simpa only [hl] using htrapped)).1.trans inf_le_right).trans
        (adjacent_Z_le d.radical p.end_color hlastAdj)
  have hcentv := (le_inf hHseeds hHz).trans hforward
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
/-- On the actual strict cube shift, a central forward triple normalizes the
full backward kernel under the original endpoint. Its cubic partner must
fail to normalize that same join. -/
theorem cube_strict_forward_triple_paired_obstruction_knownSimple
    (hb : replacementDistance h d = 4)
    (u : Equiv.Perm (Fin 6))
    (him : d.radical.map (SourceReduction.projection h e hz hn d) =
      (D 6).map (MulAut.conj u).toMonoidHom)
    {a z : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a z)
    (hstrict : 2 < (B d.radical a ((replacementGeometry h d).Z_normal _)).relIndex
      (U d.radical (p.walk.getVert 2)))
    (hforward : Z d.radical a ⊓ Z d.radical (p.walk.getVert 2) ⊓ Z d.radical z ≤
      centralizer (stabilizer d.radical (p.walk.getVert 2) : Set (FreeAmalgam d.radical))) :
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
  have hnorm := small_backward_kernel_normalized_of_triple_central s hc hb p hsmall r hr2
    hrsmall hmove q.transporter q.transporter_mem q.start_eq hforward htriple
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

include e hz hn in
/-- In the strict-forward, central-forward-triple case both cubic backward candidates
are critical, and their full kernels at the selected seed are distinct. -/
theorem cube_strict_forward_triple_distinct_kernels_knownSimple
    (hb : replacementDistance h d = 4)
    (u : Equiv.Perm (Fin 6))
    (him : d.radical.map (SourceReduction.projection h e hz hn d) =
      (D 6).map (MulAut.conj u).toMonoidHom)
    {a z : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a z)
    (hstrict : 2 < (B d.radical a ((replacementGeometry h d).Z_normal _)).relIndex
      (U d.radical (p.walk.getVert 2)))
    (hforward : Z d.radical a ⊓ Z d.radical (p.walk.getVert 2) ⊓ Z d.radical z ≤
      centralizer (stabilizer d.radical (p.walk.getVert 2) : Set (FreeAmalgam d.radical))) :
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
  obtain ⟨q,hq,hxN,hnorm,hbad⟩ := cube_strict_forward_triple_paired_obstruction_knownSimple
    (e := e) (hz := hz) (hn := hn) hb u him p hstrict hforward
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
  have hforwardx : Z d.radical a ⊓ Z d.radical (w.walk.getVert 2) ⊓
      Z d.radical (act d.radical x z) ≤
      centralizer (stabilizer d.radical (w.walk.getVert 2) : Set (FreeAmalgam d.radical)) := by
    have hh := (map_mono (f := (MulAut.conj x⁻¹).toMonoidHom) hforward).trans
      (map_centralizer_le_centralizer_image _ _)
    rw [Subgroup.map_inf _ _ _ (MulAut.conj x⁻¹).injective,
      Subgroup.map_inf _ _ _ (MulAut.conj x⁻¹).injective] at hh
    rw [←Subgroup.coe_map,←stabilizer_act] at hh
    simpa only [←Z_act,hxa,hw] using hh
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
    have hwhole := cube_trapped_forward_triple_actor_movement s hc hb u hfull w hsmall
      q.adjacent_start q.adjacent_shift htrap j hj hjc hforwardx htriplex
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
      exact small_backward_kernel_normalized_of_triple_central s hc hb w hsmall r hr
        (critical_image_small_at_knownSimple (e := e) (hz := hz) (hn := hn) hb r)
        hmove j hj hjc hforwardx htriplex
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

include e hz hn in
/-- The actual paired backward critical kernels in the strict-forward,
central-forward-triple cube branch generate the selected stabilizer with a compatible
incident edge. The projected-order premise is discharged by their proven
distinctness, retaining the same cubic and both literal endpoint seeds. -/
theorem cube_strict_forward_triple_generation_knownSimple
    (hb : replacementDistance h d = 4)
    (u : S)
    (him : d.radical.map (SourceReduction.projection h e hz hn d) =
      (D 6).map (MulAut.conj u).toMonoidHom)
    {a z : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a z)
    (hstrict : 2 < (B d.radical a ((replacementGeometry h d).Z_normal _)).relIndex
      (U d.radical (p.walk.getVert 2)))
    (hforward : Z d.radical a ⊓ Z d.radical (p.walk.getVert 2) ⊓ Z d.radical z ≤
      centralizer (stabilizer d.radical (p.walk.getVert 2) : Set (FreeAmalgam d.radical))) :
    ∃ q : EdgePairedBackwardShift (h := h) p,
      2 < (B d.radical a ((replacementGeometry h d).Z_normal _)).relIndex
        (U d.radical q.start) ∧
      q.cubic ∈ normalizer (Q d.radical (p.walk.getVert 1) : Set (FreeAmalgam d.radical)) ∧
      ∃ r : CriticalPath d.radical (replacementGeometry h d) q.start
          (act d.radical q.cubic (p.walk.getVert 2)),
        r.walk.getVert 1 = q.edge ∧ r.walk.getVert 2 = a ∧
        Z d.radical q.start ⊓ Q d.radical (p.walk.getVert 2) ≠
          Z d.radical q.start ⊓ Q d.radical (act d.radical q.cubic (p.walk.getVert 2)) ∧
        ∃ t, Adjacent d.radical q.start t ∧
          Q d.radical q.edge ⊔ Q d.radical t = stabilizer d.radical q.start ∧
          Q d.radical t ⊔ Z d.radical (p.walk.getVert 2) ⊔
            Z d.radical (act d.radical q.cubic (p.walk.getVert 2)) =
              stabilizer d.radical q.start := by
  have hb2 : 2 < replacementDistance h d := by omega
  let s := fullSymmetricAction_knownSimple h e hz hn d hb2
  have hc := DistanceTwo.centralLayer_knownSimple G L R h e hz hn d
  have hfull : d.radical.map s.projection = (D 6).map (MulAut.conj u).toMonoidHom := by
    rwa [SourceReduction.fullSymmetricAction_projection_unique h e hz hn d s]
  obtain ⟨q,hq,hx,r,hr1,hr2,hne,hlarge⟩ :=
    cube_strict_forward_triple_distinct_kernels_knownSimple
      (e := e) (hz := hz) (hn := hn) hb u him p hstrict hforward
  have hl : p.walk.length = 4 := p.length_eq_b.trans hb
  obtain ⟨p',hp'⟩ : ∃ p' : CriticalPath d.radical (replacementGeometry h d) q.start
      (p.walk.getVert 2), p'.walk.getVert 1 = q.edge := by
    have hh : ∃ p' : CriticalPath d.radical (replacementGeometry h d) q.start
        (p.walk.getVert (p.walk.length-2)), p'.walk.getVert 1 = q.edge := ⟨q.path,q.first⟩
    have hl2 : p.walk.length - 2 = 2 := by omega
    rw [hl2] at hh
    exact hh
  have endpoint_le {w : Vertex d.radical}
      (v : CriticalPath d.radical (replacementGeometry h d) q.start w)
      (hv : v.walk.getVert 1 = q.edge) : Z d.radical w ≤ Q d.radical q.edge := by
    apply Z_le_Q_of_dist_lt d.radical w ((replacementGeometry h d).exists_critical w v.end_color)
    rw [←hv,SimpleGraph.dist_comm,v.dist_end,(replacementGeometry h d).distance_constant w v.end_color]
    have hh : v.walk.length = replacementDistance h d := v.length_eq_b
    change v.walk.length-1 < replacementDistance h d
    omega
  let W := Z d.radical (p.walk.getVert 2) ⊔
    Z d.radical (act d.radical q.cubic (p.walk.getVert 2))
  have hW : W ≤ Q d.radical (p'.walk.getVert 1) := by
    rw [hp']
    exact sup_le (endpoint_le p' hp') (endpoint_le r hr1)
  obtain ⟨t,ht,hfirst,hgen⟩ := cube_nonline_neighbor s hc u hfull p'
    (critical_image_small_at_knownSimple (e := e) (hz := hz) (hn := hn) hb p') W hW hlarge
  refine ⟨q,hq,hx,r,hr1,hr2,hne,t,ht,?_,?_⟩
  · simpa only [hp'] using hfirst
  · simpa only [W,sup_assoc] using hgen

include e hz hn in
/-- A strict forward cube slice cannot have a central forward seed triple. -/
theorem cube_strict_forward_triple_false_knownSimple
    (hb : replacementDistance h d = 4) (u : Equiv.Perm (Fin 6))
    (him : d.radical.map (SourceReduction.projection h e hz hn d) =
      (D 6).map (MulAut.conj u).toMonoidHom)
    {a z : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a z)
    (hstrict : 2 < (B d.radical a ((replacementGeometry h d).Z_normal _)).relIndex
      (U d.radical (p.walk.getVert 2)))
    (hforward : Z d.radical a ⊓ Z d.radical (p.walk.getVert 2) ⊓ Z d.radical z ≤
      centralizer (stabilizer d.radical (p.walk.getVert 2) : Set (FreeAmalgam d.radical))) : False := by
  have hb2 : 2 < replacementDistance h d := by omega
  let s := fullSymmetricAction_knownSimple h e hz hn d hb2
  have hc := DistanceTwo.centralLayer_knownSimple G L R h e hz hn d
  have hfull : d.radical.map s.projection = (D 6).map (MulAut.conj u).toMonoidHom := by
    rwa [SourceReduction.fullSymmetricAction_projection_unique h e hz hn d s]
  obtain ⟨q,hq,hxN,r,hr1,hr2,_,t,ht,hfirst,hactors⟩ :=
    cube_strict_forward_triple_generation_knownSimple
      (e := e) (hz := hz) (hn := hn) hb u him p hstrict hforward
  have hl : p.walk.length = 4 := p.length_eq_b.trans hb
  obtain ⟨q₀,hq₀2⟩ : ∃ q₀ : CriticalPath d.radical (replacementGeometry h d)
      q.start (p.walk.getVert 2), q₀.walk.getVert 2 = a := by
    have hh : ∃ q₀ : CriticalPath d.radical (replacementGeometry h d)
        q.start (p.walk.getVert (p.walk.length-2)), q₀.walk.getVert 2 = a := by
      refine ⟨q.path,?_⟩
      simpa only [Nat.zero_add,SimpleGraph.Walk.getVert_zero] using q.overlap 0 (by omega)
    rw [show p.walk.length-2=2 by omega] at hh
    exact hh
  have hat : Adjacent d.radical a (p.walk.getVert 1) := by
    apply (cosetGraph_adj d.radical _ _).mp
    simpa only [SimpleGraph.Walk.getVert_zero] using p.walk.adj_getVert_succ (i := 0) (by omega)
  have hvt : Adjacent d.radical (p.walk.getVert 2) (p.walk.getVert 1) :=
    adjacent_symm d.radical ((cosetGraph_adj d.radical _ _).mp
      (p.walk.adj_getVert_succ (i := 1) (by omega)))
  have tripleV : Z d.radical q.start ⊓ Z d.radical a ⊓ Z d.radical (p.walk.getVert 2) ≤
      centralizer (stabilizer d.radical a : Set (FreeAmalgam d.radical)) := by
    have hh := cube_strict_compatible_triple_central s hb2 u hfull p.start_color hat hvt
      q.adjacent_start q.adjacent_shift hstrict hq q.first_kernel_generation
    have he : Z d.radical q.start ⊓ Z d.radical a ⊓ Z d.radical (p.walk.getVert 2) =
        Z d.radical (p.walk.getVert 2) ⊓ Z d.radical a ⊓ Z d.radical q.start := by ac_rfl
    rwa [he]
  let x := q.cubic
  have hx : x ∈ stabilizer d.radical a := Ltilde_le_stabilizer _ q.cubic_mem
  have hxa : act d.radical x a = a := hx
  have hxstrict : 2 < (B d.radical a ((replacementGeometry h d).Z_normal _)).relIndex
      (U d.radical (act d.radical x (p.walk.getVert 2))) := by
    have hB := Escape.PairingControl.FirstPairing.B_act
      (geometry := replacementGeometry h d) hb2 x a p.start_color
    rw [hxa] at hB
    rw [hB,U_act,relIndex_map_map_of_injective _ _ (MulAut.conj _).injective]
    exact hstrict
  have hax : Adjacent d.radical a (act d.radical x (p.walk.getVert 1)) := by
    simpa only [hxa] using (adjacent_act_iff d.radical x _ _).mpr hat
  have hvx : Adjacent d.radical (act d.radical x (p.walk.getVert 2))
      (act d.radical x (p.walk.getVert 1)) := (adjacent_act_iff d.radical x _ _).mpr hvt
  have hQx : Q d.radical (act d.radical x (p.walk.getVert 1)) =
      Q d.radical (p.walk.getVert 1) := by
    rw [Q_act]
    exact mem_normalizer_iff_map_conj_eq.mp
      ((normalizer (Q d.radical (p.walk.getVert 1) : Set (FreeAmalgam d.radical))).inv_mem hxN)
  have tripleW : Z d.radical q.start ⊓ Z d.radical a ⊓
      Z d.radical (act d.radical x (p.walk.getVert 2)) ≤
      centralizer (stabilizer d.radical a : Set (FreeAmalgam d.radical)) := by
    have hh := cube_strict_compatible_triple_central s hb2 u hfull p.start_color hax hvx
      q.adjacent_start q.adjacent_shift hxstrict hq
      (by rw [hQx]; exact q.first_kernel_generation)
    have he : Z d.radical q.start ⊓ Z d.radical a ⊓
          Z d.radical (act d.radical x (p.walk.getVert 2)) =
        Z d.radical (act d.radical x (p.walk.getVert 2)) ⊓ Z d.radical a ⊓ Z d.radical q.start := by
      ac_rfl
    rwa [he]
  let k := x⁻¹ * q.transporter
  have hk : k ∈ stabilizer d.radical a := mul_mem (inv_mem hx) q.transporter_mem
  have hkw : act d.radical k (act d.radical x (p.walk.getVert 2)) = q.start := by
    have hcancel (v : Vertex d.radical) : act d.radical x⁻¹ (act d.radical x v) = v := by
      rw [←act_mul,mul_inv_cancel,act_one]
    rw [show k=x⁻¹*q.transporter from rfl,act_mul,hcancel]
    exact q.start_eq
  exact cube_paired_second_backward_strict_false s hc hb u hfull q₀ r hq₀2 hr2
    q.adjacent_start q.adjacent_shift ht hq hfirst hactors
    q.transporter q.transporter_mem q.start_eq k hk hkw tripleV tripleW

end AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.Terminal
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
