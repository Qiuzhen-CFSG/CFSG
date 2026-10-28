module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.PredecessorResidual
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.InitialSelection
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.CubeAlignment
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.BackwardRigidity

/-!
# Residual rotation and the full midpoint radius at distance four

Let a--v--c--w--z be an original critical path of length four, and suppose
that the predecessor moving slice U_z modulo B_c has order at most two.
The full critical kernel K = Z_z intersect Q_a lies in B_c, and the previous
whole-core estimate makes [K,Q_c] fixed by the midpoint residual. Rotating
w onto v takes each seed incident to v within distance two of z. Exact
commutator transport therefore makes K fix every such seed. Residual
transitivity propagates this to the whole midpoint radius V_c.

The critical transposition fixes exactly K on Z_z. Consequently V_c has
image of order two at z, its displacement on the full Z_z is the original
critical line, and its full fixed subgroup in Z_z is K. These are statements
about the entire radius and seed, with both moving covers and every central
attachment retained; no radical-image specialization is used.

For the small-image alternative in source (5.8), a nonzero commutator of K
with a seed Z_delta lying in Q_c and incident to a forces a literal rotated
critical path delta--t--a--v--z^k. Its edge t differs from v. Uniformly small
critical images make the new full displacement equal to that nonzero kernel
commutator. If it lies in the old critical line times the actual endpoint
center, the full-cover aligned-actor calculation instead makes it trivial.
The last theorem applies this contradiction to the original initial-selection
alternative and produces a nonabelian large-slice path.

Constructing the required small predecessor slice and aligned nonzero moving
seed from the original hypotheses remains part of initial selection. The
separately owned selected terminal family and final DistanceFourInput assembly
also remain open. No selector or terminal callback is assumed in these proofs.
The private import reuses the checked residual neighbor transporter without
changing the public boundary of BackwardRigidity.

Source: Meierfrankenfeld--Stellmacher, *Pushing up weak BN-pairs of rank two*
(1993), (5.8), printed pp.919--920, and its use in (5.12), p.924.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped commutatorElement Pointwise
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour
universe u
variable {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
  {h : SmallMSPair KnownSimple.IsKnownSimple L R} {e : CentralMarking L}
  {hz : center (L ⧸ pCore 2 L) = ⊥} {hn : InitialNatural h e hz}
  {d : Replacement L R}

omit [Finite G] in
private theorem common_neighbor_distance {a c t : Vertex d.radical}
    (hat : Adjacent d.radical a t) (hct : Adjacent d.radical c t) :
    (cosetGraph d.radical).dist a c ≤ 2 := by
  have h1 : (cosetGraph d.radical).dist a t = 1 :=
    SimpleGraph.dist_eq_one_iff_adj.mpr ((cosetGraph_adj d.radical _ _).mpr hat)
  have h2 : (cosetGraph d.radical).dist t c = 1 :=
    SimpleGraph.dist_eq_one_iff_adj.mpr
      ((cosetGraph_adj d.radical _ _).mpr (adjacent_symm d.radical hct))
  simpa only [h1,h2] using (cosetGraph_connected d.radical).dist_triangle
    (u := a) (v := t) (w := c)

include e hz hn in
/-- The full critical kernel fixes every seed incident to the first edge.
The last-edge rotation and commutator transport retain the full central seed. -/
theorem small_predecessor_first_edge_fixed_knownSimple
    (hb : replacementDistance h d = 4) {a z : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a z)
    (hslice : (B d.radical (p.walk.getVert 2) ((replacementGeometry h d).Z_normal _)).relIndex
      (U d.radical z) ≤ 2)
    {delta : Vertex d.radical} (hdelta : Adjacent d.radical delta (p.walk.getVert 1)) :
    ⁅Z d.radical z ⊓ Q d.radical a,Z d.radical delta⁆ = ⊥ := by
  have hl : p.walk.length = 4 := p.length_eq_b.trans hb
  have hcv : Adjacent d.radical (p.walk.getVert 2) (p.walk.getVert 1) :=
    adjacent_symm d.radical ((cosetGraph_adj d.radical _ _).mp
      (p.walk.adj_getVert_succ (i := 1) (by omega)))
  have hcCol : color d.radical (p.walk.getVert 2) = false :=
    (p.vertex_color (by omega)).mpr (by decide)
  have hdeltaCol : color d.radical delta = false := by
    have h1 := adjacent_color_ne d.radical hcv
    have h2 := adjacent_color_ne d.radical hdelta
    rw [hcCol] at h1
    cases hd : color d.radical delta <;>
      cases hv : color d.radical (p.walk.getVert 1) <;> simp_all
  have hD : Z d.radical delta ≤ Q d.radical (p.walk.getVert 2) := by
    apply Z_le_Q_of_dist_lt d.radical delta
      ((replacementGeometry h d).exists_critical delta hdeltaCol)
    rw [(replacementGeometry h d).distance_constant delta hdeltaCol]
    have hh := common_neighbor_distance hdelta hcv
    change (cosetGraph d.radical).dist delta (p.walk.getVert 2) < replacementDistance h d
    omega
  obtain ⟨_,_,_,k,hk,hkt,htransport,_⟩ :=
    small_predecessor_residual_shift_knownSimple (e := e) (hz := hz) (hn := hn) hb p hslice
  have hzt : Adjacent d.radical z (p.walk.getVert 3) := by
    have hh := p.walk.adj_getVert_succ (i := 3) (by omega)
    rw [show 3 + 1 = p.walk.length by omega,p.walk.getVert_length] at hh
    exact adjacent_symm d.radical ((cosetGraph_adj d.radical _ _).mp hh)
  have hkz : Adjacent d.radical (act d.radical k z) (p.walk.getVert 1) := by
    rw [←hkt]
    exact (adjacent_act_iff d.radical k _ _).mpr hzt
  have hnear := common_neighbor_distance hdelta hkz
  have hDk : Z d.radical (act d.radical k⁻¹ delta) ≤ Q d.radical z := by
    have hDQ : Z d.radical delta ≤ Q d.radical (act d.radical k z) := by
      apply Z_le_Q_of_dist_lt d.radical delta
        ((replacementGeometry h d).exists_critical delta hdeltaCol)
      rw [(replacementGeometry h d).distance_constant delta hdeltaCol]
      change (cosetGraph d.radical).dist delta (act d.radical k z) < replacementDistance h d
      omega
    calc
      _ = (Z d.radical delta).map (MulAut.conj k).toMonoidHom := by rw [Z_act,inv_inv]
      _ ≤ (Q d.radical (act d.radical k z)).map (MulAut.conj k).toMonoidHom := map_mono hDQ
      _ = Q d.radical (act d.radical k⁻¹ (act d.radical k z)) := by
        simpa only [inv_inv] using (Q_act d.radical k⁻¹ (act d.radical k z)).symm
      _ = Q d.radical z := by rw [←act_mul,mul_inv_cancel,act_one]
  rw [←(htransport delta hD).1]
  exact le_bot_iff.mp ((commutator_mono inf_le_left hDk).trans_eq
    (Z_centralizes_Q d.radical z p.end_color))

include e hz hn in
/-- A nonzero full-kernel commutator constructs the actual rotated critical
path through the original base and first edge. No small-image assumption is needed. -/
theorem small_predecessor_residual_critical_path_knownSimple
    (hb : replacementDistance h d = 4) {a z delta t : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a z)
    (hslice : (B d.radical (p.walk.getVert 2) ((replacementGeometry h d).Z_normal _)).relIndex
      (U d.radical z) ≤ 2)
    (hat : Adjacent d.radical a t) (hdelta : Adjacent d.radical delta t)
    (hD : Z d.radical delta ≤ Q d.radical (p.walk.getVert 2))
    (hne : ⁅Z d.radical z ⊓ Q d.radical a,Z d.radical delta⁆ ≠ ⊥) :
    t ≠ p.walk.getVert 1 ∧
      ∃ k ∈ Ltilde d.radical (p.walk.getVert 2),
        act d.radical k (p.walk.getVert 3) = p.walk.getVert 1 ∧
        ∃ q : CriticalPath d.radical (replacementGeometry h d) delta (act d.radical k z),
          q.walk.getVert 1 = t ∧ q.walk.getVert 2 = a ∧
          q.walk.getVert 3 = p.walk.getVert 1 ∧
          ⁅Z d.radical z ⊓ Q d.radical a,Z d.radical (act d.radical k⁻¹ delta)⁆ =
            ⁅Z d.radical z ⊓ Q d.radical a,Z d.radical delta⁆ := by
  have hl : p.walk.length = 4 := p.length_eq_b.trans hb
  have ht : t ≠ p.walk.getVert 1 := by
    intro he
    exact hne (small_predecessor_first_edge_fixed_knownSimple
      (e := e) (hz := hz) (hn := hn) hb p hslice (he ▸ hdelta))
  obtain ⟨_,_,_,k,hk,hkt,htransport,_⟩ :=
    small_predecessor_residual_shift_knownSimple (e := e) (hz := hz) (hn := hn) hb p hslice
  have hescape : ¬ Z d.radical delta ≤ Q d.radical (act d.radical k z) := by
    intro hh
    have hm : Z d.radical (act d.radical k⁻¹ delta) ≤ Q d.radical z := by
      calc
        _ = (Z d.radical delta).map (MulAut.conj k).toMonoidHom := by rw [Z_act,inv_inv]
        _ ≤ (Q d.radical (act d.radical k z)).map (MulAut.conj k).toMonoidHom := map_mono hh
        _ = Q d.radical (act d.radical k⁻¹ (act d.radical k z)) := by
          simpa only [inv_inv] using (Q_act d.radical k⁻¹ (act d.radical k z)).symm
        _ = Q d.radical z := by rw [←act_mul,mul_inv_cancel,act_one]
    apply hne
    rw [←(htransport delta hD).1]
    exact le_bot_iff.mp ((commutator_mono inf_le_left hm).trans_eq
      (Z_centralizes_Q d.radical z p.end_color))
  have hdeltaCol : color d.radical delta = false := by
    have h1 := adjacent_color_ne d.radical hat
    have h2 := adjacent_color_ne d.radical hdelta
    rw [p.start_color] at h1
    cases hd : color d.radical delta <;> cases hv : color d.radical t <;> simp_all
  have hav : Adjacent d.radical a (p.walk.getVert 1) := by
    apply (cosetGraph_adj d.radical _ _).mp
    simpa only [SimpleGraph.Walk.getVert_zero] using
      p.walk.adj_getVert_succ (i := 0) (by omega)
  have hzt : Adjacent d.radical (p.walk.getVert 3) z := by
    have hh := p.walk.adj_getVert_succ (i := 3) (by omega)
    rw [show 3 + 1 = p.walk.length by omega,p.walk.getVert_length] at hh
    exact (cosetGraph_adj d.radical _ _).mp hh
  have hvz : Adjacent d.radical (p.walk.getVert 1) (act d.radical k z) := by
    rw [←hkt]
    exact (adjacent_act_iff d.radical k _ _).mpr hzt
  let w : (cosetGraph d.radical).Walk delta (act d.radical k z) :=
    .cons ((cosetGraph_adj d.radical _ _).mpr hdelta)
      (.cons ((cosetGraph_adj d.radical _ _).mpr (adjacent_symm d.radical hat))
        (.cons ((cosetGraph_adj d.radical _ _).mpr hav)
          (.cons ((cosetGraph_adj d.radical _ _).mpr hvz) .nil)))
  have hw : w.length = 4 := rfl
  have hmin := criticalDistance_le d.radical delta
    ((replacementGeometry h d).exists_critical delta hdeltaCol) hescape
  rw [(replacementGeometry h d).distance_constant delta hdeltaCol] at hmin
  have hdist : (cosetGraph d.radical).dist delta (act d.radical k z) = replacementDistance h d := by
    have hh := SimpleGraph.dist_le w
    rw [hw] at hh
    exact le_antisymm (by simpa only [hb] using hh) hmin
  let q : CriticalPath d.radical (replacementGeometry h d) delta (act d.radical k z) :=
    ⟨hdeltaCol,w,hw.trans (hb.symm.trans hdist.symm),by
      refine ⟨?_,hescape⟩
      rw [(replacementGeometry h d).distance_constant delta hdeltaCol]
      exact hdist⟩
  exact ⟨ht,k,hk,hkt,q,rfl,rfl,rfl,(htransport delta hD).1⟩

include e hz hn in
/-- A small predecessor slice makes the full reverse critical kernel
centralize the entire midpoint radius, for every radical image and both covers. -/
theorem small_predecessor_midpoint_radius_fixed_knownSimple
    (hb : replacementDistance h d = 4) {a z : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a z)
    (hslice : (B d.radical (p.walk.getVert 2) ((replacementGeometry h d).Z_normal _)).relIndex
      (U d.radical z) ≤ 2) :
    Z d.radical z ⊓ Q d.radical a ≤
      centralizer (V d.radical (p.walk.getVert 2) : Set (FreeAmalgam d.radical)) := by
  let s := fullSymmetricAction_knownSimple h e hz hn d (by omega)
  have hc := DistanceTwo.centralLayer_knownSimple G L R h e hz hn d
  have hl : p.walk.length = 4 := p.length_eq_b.trans hb
  let c := p.walk.getVert 2
  have hcCol : color d.radical c = false := (p.vertex_color (by omega)).mpr (by decide)
  have hcv : Adjacent d.radical c (p.walk.getVert 1) :=
    adjacent_symm d.radical ((cosetGraph_adj d.radical _ _).mp
      (p.walk.adj_getVert_succ (i := 1) (by omega)))
  have hzc : (cosetGraph d.radical).dist z c = 2 := by
    rw [SimpleGraph.dist_comm,p.dist_end,hl]
  have hKQ : Z d.radical z ⊓ Q d.radical a ≤ Q d.radical c := by
    apply inf_le_left.trans
    apply Z_le_Q_of_dist_lt d.radical z ((replacementGeometry h d).exists_critical z p.end_color)
    rw [(replacementGeometry h d).distance_constant z p.end_color,hzc]
    exact show 2 < replacementDistance h d by omega
  apply le_centralizer_iff.mpr
  apply (V_le_iff d.radical hcCol _).mpr
  intro delta hdeltaCol hdist
  by_cases he : delta = c
  · subst delta
    exact (commutator_eq_bot_iff_le_centralizer.mp (Z_centralizes_Q d.radical c hcCol)).trans
      (centralizer_le hKQ)
  have htwo : (cosetGraph d.radical).dist c delta = 2 := by
    have hne : (cosetGraph d.radical).dist c delta ≠ 0 := by
      intro hz
      exact he ((cosetGraph_connected d.radical).dist_eq_zero_iff.mp hz).symm
    have heven : Even ((cosetGraph d.radical).dist c delta) := by
      obtain ⟨w,hw⟩ := (cosetGraph_connected d.radical).exists_walk_length_eq_dist c delta
      rw [←hw,walk_even_iff_color_eq,hcCol,hdeltaCol]
    rw [Nat.even_iff] at heven
    rw [SimpleGraph.dist_comm] at hdist
    omega
  obtain ⟨t,hct,hdt⟩ := exists_common_neighbor_of_dist_two d.radical c delta htwo
  obtain ⟨k,hk,hkt⟩ := residual_neighbor_transporter (h := h) hcCol hcv hct
  have hD : Z d.radical delta ≤ Q d.radical c := by
    apply Z_le_Q_of_dist_lt d.radical delta
      ((replacementGeometry h d).exists_critical delta hdeltaCol)
    rw [(replacementGeometry h d).distance_constant delta hdeltaCol]
    change (cosetGraph d.radical).dist delta c < replacementDistance h d
    omega
  have hdk : Adjacent d.radical (act d.radical k⁻¹ delta) (p.walk.getVert 1) := by
    have hh := (adjacent_act_iff d.radical k⁻¹ _ _).mpr hdt
    rw [←hkt,←act_mul,mul_inv_cancel,act_one] at hh
    exact hh
  have hzero := small_predecessor_first_edge_fixed_knownSimple
    (e := e) (hz := hz) (hn := hn) hb p hslice hdk
  have htransport :
      ⁅Z d.radical z ⊓ Q d.radical a,Z d.radical (act d.radical k⁻¹ delta)⁆ =
        ⁅Z d.radical z ⊓ Q d.radical a,Z d.radical delta⁆ := by
    rw [Z_act,inv_inv]
    exact small_predecessor_whole_core_transport s hc hb p hslice _ hD k hk
  exact le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp
    (htransport.symm.trans hzero))

include e hz hn in
/-- The whole midpoint radius has exactly the original critical image at
the endpoint, its full-seed displacement line, and its full critical fixed kernel. -/
theorem small_predecessor_midpoint_radius_image_knownSimple
    (hb : replacementDistance h d = 4) {a z : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a z)
    (hslice : (B d.radical (p.walk.getVert 2) ((replacementGeometry h d).Z_normal _)).relIndex
      (U d.radical z) ≤ 2) :
    let W := V d.radical (p.walk.getVert 2)
    (Q d.radical z).relIndex W = 2 ∧
      Q d.radical z ⊔ W = Q d.radical z ⊔ Z d.radical a ∧
      ⁅Z d.radical z,W⁆ = ⁅Z d.radical z,Z d.radical a⁆ ∧
      Z d.radical z ⊓ centralizer (W : Set (FreeAmalgam d.radical)) =
        Z d.radical z ⊓ Q d.radical a := by
  dsimp only
  have hb2 : 2 < replacementDistance h d := by omega
  let s := fullSymmetricAction_knownSimple h e hz hn d hb2
  have hc := DistanceTwo.centralLayer_knownSimple G L R h e hz hn d
  have hl : p.walk.length = 4 := p.length_eq_b.trans hb
  have hs := critical_predecessor_slice_eq_kernel s hc hb2 p (by simpa only [hl] using hslice)
  have hsmall : (Q d.radical z).relIndex (Z d.radical a) < 4 := by rw [hs.2.1]; decide
  let c := p.walk.getVert 2
  let W := V d.radical c
  have hcCol : color d.radical c = false := (p.vertex_color (by omega)).mpr (by decide)
  have hcz : (cosetGraph d.radical).dist c z = 2 := by rw [p.dist_end,hl]
  have hac : (cosetGraph d.radical).dist a c = 2 := p.dist_start (by omega)
  have hAW : Z d.radical a ≤ W := le_iSup_of_le a (le_iSup_of_le hac.le le_rfl)
  have hWG : W ≤ stabilizer d.radical z :=
    (V_le_Q d.radical hcCol hb2).trans (Q_le_stabilizer_of_dist_two d.radical c z hcCol hcz)
  have hfix := small_predecessor_midpoint_radius_fixed_knownSimple
    (e := e) (hz := hz) (hn := hn) hb p hslice
  have hcomm : ⁅Z d.radical z,W⁆ = ⁅Z d.radical z,Z d.radical a⁆ := by
    apply le_antisymm
    · rw [commutator_comm]
      have hh := small_critical_kernel_commutator s hc p hsmall W hWG
        (le_centralizer_iff.mp hfix)
      rwa [commutator_comm (Z d.radical a) (Z d.radical z)] at hh
    · exact commutator_mono le_rfl hAW
  have hWle : W ≤ Q d.radical z ⊔ Z d.radical a := by
    apply small_critical_aligned_actor_le s hc p hsmall W hWG
    exact ((commutator_mono (DistanceEight.U_le_Z d.radical z) le_rfl).trans_eq hcomm).trans
      (by rw [commutator_comm]; exact le_sup_left)
  have hsup : Q d.radical z ⊔ W = Q d.radical z ⊔ Z d.radical a :=
    le_antisymm (sup_le le_sup_left hWle) (sup_le_sup_left hAW _)
  have hindex (D : Subgroup (FreeAmalgam d.radical))
      (hDn : D ≤ normalizer (Q d.radical z : Set (FreeAmalgam d.radical))) :
      (Q d.radical z).relIndex (Q d.radical z ⊔ D) = (Q d.radical z).relIndex D := by
    let J := Q d.radical z ⊔ D
    let : ((Q d.radical z).subgroupOf J).Normal :=
      normal_subgroupOf_of_le_normalizer (sup_le (Q d.radical z).le_normalizer hDn)
    have hi := relIndex_sup_left (D.subgroupOf J) ((Q d.radical z).subgroupOf J)
    rw [←subgroupOf_sup le_sup_left le_sup_right,relIndex_subgroupOf le_rfl,
      relIndex_subgroupOf le_sup_right] at hi
    exact hi
  have hi : (Q d.radical z).relIndex W = 2 := by
    rw [←hindex W (hWG.trans (Q_normalized d.radical z)),hsup,
      hindex (Z d.radical a) ((hAW.trans hWG).trans (Q_normalized d.radical z)),hs.2.1]
  refine ⟨hi,hsup,hcomm,le_antisymm ?_ (le_inf inf_le_left hfix)⟩
  apply le_inf inf_le_left
  rw [←C_eq_Q s hc a p.start_color]
  exact le_inf (inf_le_left.trans (critical_Z_le_stabilizer d.radical
    (replacementGeometry h d) a p.start_color (by
      rw [(replacementGeometry h d).distance_constant a p.start_color]
      exact replacementDistance_pos h d) p.critical))
    (inf_le_right.trans (centralizer_le hAW))

private theorem uniformly_small_critical_index_at
    (hsmall : ∀ z, ∀ _p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) z,
      (Q d.radical z).relIndex (Z d.radical (alpha d.radical)) < 4)
    {a z : Vertex d.radical} (p : CriticalPath d.radical (replacementGeometry h d) a z) :
    (Q d.radical z).relIndex (Z d.radical a) < 4 := by
  obtain ⟨j,hj⟩ := exists_mVertex_of_color d.radical p.start_color
  have hbase : act d.radical j⁻¹ a = alpha d.radical := by
    rw [hj,act_mVertex,mul_inv_cancel]
    rfl
  have hs : ∀ q : CriticalPath d.radical (replacementGeometry h d)
      (act d.radical j⁻¹ a) (act d.radical j⁻¹ z),
      (Q d.radical (act d.radical j⁻¹ z)).relIndex (Z d.radical (act d.radical j⁻¹ a)) < 4 := by
    rw [hbase]
    exact hsmall _
  have hi := hs (p.act j⁻¹)
  simp only [Q_act,Z_act,inv_inv] at hi
  rwa [relIndex_map_map_of_injective _ _ (MulAut.conj j).injective] at hi

include e hz hn in
/-- In the uniformly small-image alternative, a nearby seed whose kernel
commutator is aligned with the old critical line and actual endpoint center must
fix the full kernel. The proof constructs the residual-rotated critical path. -/
theorem small_images_small_predecessor_aligned_kernel_fixed_knownSimple
    (hb : replacementDistance h d = 4)
    (hsmall : ∀ z, ∀ _p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) z,
      (Q d.radical z).relIndex (Z d.radical (alpha d.radical)) < 4)
    {a z delta t : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a z)
    (hslice : (B d.radical (p.walk.getVert 2) ((replacementGeometry h d).Z_normal _)).relIndex
      (U d.radical z) ≤ 2)
    (hat : Adjacent d.radical a t) (hdelta : Adjacent d.radical delta t)
    (hD : Z d.radical delta ≤ Q d.radical (p.walk.getVert 2))
    (halign : ⁅Z d.radical z ⊓ Q d.radical a,Z d.radical delta⁆ ≤
      ⁅Z d.radical a,Z d.radical z⁆ ⊔
        (stabilizer d.radical z ⊓ centralizer (stabilizer d.radical z : Set (FreeAmalgam d.radical)))) :
    ⁅Z d.radical z ⊓ Q d.radical a,Z d.radical delta⁆ = ⊥ := by
  by_contra hne
  have hb2 : 2 < replacementDistance h d := by omega
  let s := fullSymmetricAction_knownSimple h e hz hn d hb2
  have hc := DistanceTwo.centralLayer_knownSimple G L R h e hz hn d
  have hl : p.walk.length = 4 := p.length_eq_b.trans hb
  obtain ⟨_,k,hk,_,q,_,_,_,htransport⟩ :=
    small_predecessor_residual_critical_path_knownSimple
      (e := e) (hz := hz) (hn := hn) hb p hslice hat hdelta hD hne
  have hqsmall := uniformly_small_critical_index_at (h := h) hsmall q
  let qr := CriticalPath.ofPair (geometry := replacementGeometry h d) q.end_color
    (critical_reverse_pair s hc q)
  have hqrsmall : (Q d.radical delta).relIndex (Z d.radical (act d.radical k z)) < 4 := by
    rw [(small_critical_indices s hc q hqsmall).2]
    decide
  let H := ⁅Z d.radical z ⊓ Q d.radical a,Z d.radical delta⁆
  let D := ⁅Z d.radical z,Z d.radical (act d.radical k⁻¹ delta)⁆
  have hcardD : Nat.card D = 2 := by
    dsimp only [D]
    rw [←card_map_of_injective (f := (MulAut.conj k⁻¹).toMonoidHom)
      (MulAut.conj k⁻¹).injective,map_commutator]
    have hZ : (Z d.radical (act d.radical k⁻¹ delta)).map (MulAut.conj k⁻¹).toMonoidHom =
        Z d.radical delta := by
      rw [←Z_act,←act_mul,inv_mul_cancel,act_one]
    rw [←Z_act,hZ]
    exact small_critical_commutator_card s hc qr hqrsmall
  have hmove : ⁅U d.radical z,Z d.radical (act d.radical k⁻¹ delta)⁆ = D := by
    apply (map_injective (f := (MulAut.conj k⁻¹).toMonoidHom) (MulAut.conj k⁻¹).injective)
    dsimp only [D]
    rw [map_commutator,map_commutator,←U_act,←Z_act,←Z_act,←act_mul,inv_mul_cancel,act_one]
    exact small_critical_moving_commutator_eq s hc qr hqrsmall
  have hHD : H ≤ D := by
    rw [show H = ⁅Z d.radical z ⊓ Q d.radical a,Z d.radical (act d.radical k⁻¹ delta)⁆
      from htransport.symm]
    exact commutator_mono inf_le_left le_rfl
  let : Finite D := Nat.finite_of_card_ne_zero (by rw [hcardD]; decide)
  let : Finite H := Finite.of_injective (inclusion hHD) (inclusion_injective _)
  have hpos : 1 < Nat.card H := (one_lt_card_iff_ne_bot H).mpr hne
  have heq : D = H := (eq_of_le_of_card_ge hHD (by omega)).symm
  have hDk : Z d.radical (act d.radical k⁻¹ delta) ≤ Q d.radical (p.walk.getVert 2) := by
    rw [Z_act,inv_inv]
    exact (map_mono hD).trans_eq (mem_normalizer_iff_map_conj_eq.mp
      ((Q_normalized d.radical _) (Ltilde_le_stabilizer _ hk)))
  have hcCol : color d.radical (p.walk.getVert 2) = false :=
    (p.vertex_color (by omega)).mpr (by decide)
  have hcz : (cosetGraph d.radical).dist (p.walk.getVert 2) z = 2 := by rw [p.dist_end,hl]
  have hzero := small_critical_aligned_kernel_commutator_eq_bot s hc p
    (uniformly_small_critical_index_at (h := h) hsmall p)
    (Z d.radical (act d.radical k⁻¹ delta))
    (hDk.trans (Q_le_stabilizer_of_dist_two d.radical _ _ hcCol hcz))
    (by rw [hmove,heq]; exact halign)
  exact hne (htransport.symm.trans hzero)

include e hz hn in
/-- The literal initial-selection consumer of source (5.8)'s aligned
kernel obstruction. The small predecessor slice and its nonzero aligned seed
remain explicit source premises; no nonabelian selected span is assumed. -/
theorem initial_selection_of_aligned_kernel_movement_knownSimple
    (hb : replacementDistance h d = 4) {a z delta t : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a z)
    (hslice : (B d.radical (p.walk.getVert 2) ((replacementGeometry h d).Z_normal _)).relIndex
      (U d.radical z) ≤ 2)
    (hat : Adjacent d.radical a t) (hdelta : Adjacent d.radical delta t)
    (hD : Z d.radical delta ≤ Q d.radical (p.walk.getVert 2))
    (hne : ⁅Z d.radical z ⊓ Q d.radical a,Z d.radical delta⁆ ≠ ⊥)
    (halign : ⁅Z d.radical z ⊓ Q d.radical a,Z d.radical delta⁆ ≤
      ⁅Z d.radical a,Z d.radical z⁆ ⊔
        (stabilizer d.radical z ⊓ centralizer (stabilizer d.radical z : Set (FreeAmalgam d.radical)))) :
    ∃ w, ∃ r : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) w,
      ⁅localZSpan d.radical (r.walk.getVert 2) (alpha d.radical),
        localZSpan d.radical (r.walk.getVert 2) (alpha d.radical)⁆ ≠ ⊥ ∧
      2 < (B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _)).relIndex
        (U d.radical (r.walk.getVert 2)) := by
  rcases initial_selection_or_cube_radius_knownSimple (e := e) (hz := hz) (hn := hn) hb with hsel | hs
  · exact hsel
  exact False.elim (hne (small_images_small_predecessor_aligned_kernel_fixed_knownSimple
    (e := e) (hz := hz) (hn := hn) hb (fun w r => by rw [(hs.2.1 w r).1]; decide)
    p hslice hat hdelta hD halign))

end AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
