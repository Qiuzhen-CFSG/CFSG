module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.LargeImage

/-!
# Full restricted endpoint seeds and backward kernels at distance four

For a critical pair with seed image of order at least four, restrict the
opposite moving cover by the original six-letter commutator calculation.
Keeping its preserved commutator gives an exact identity on the whole
radius intersection with the predecessor core. Adjoining the entire
last-edge central seed then yields a subgroup E of the full endpoint seed,
of index at most two, with

  [Z_start,E] = [V_start ∩ Q_predecessor,E] = [Z_start,Z_end].

At distance four this controls every backward moving kernel
K = U_z ∩ Q_mid with z in the starting radius. In particular E normalizes
K Z_start and its commutator on that join is the original critical
commutator. The final application constructs the conjugate backward
critical path from the large-image data and supplies these estimates on
its literal endpoint, midpoint and conjugator.

The original radical, both moving covers and full central attachments are
retained. E is constructed here; no equality with a separately prescribed
restricted seed is asserted. This supplies the large-image restricted-seed
normalization calculation used in MS93 (5.12)(1), not the whole of (1).
Small-image initial selection, compatibility with the subsequent source
choices, large-slice exclusion and whole residual-core upper estimates
remain necessary for DistanceFourInput.

Source: Meierfrankenfeld--Stellmacher, *Pushing up weak BN-pairs of rank two*
(1993), (3.3)(ii), printed pp.866--867, (5.2)(i), pp.913--914, and
(5.12)(1), pp.924--925. The moving-actor construction sharpens
SectionFive.CoreRestriction on the same injective vertex coordinates.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped commutatorElement Pointwise IsMulCommutative
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
open CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour
universe u
variable {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
  {h : SmallMSPair KnownSimple.IsKnownSimple L R} {e : CentralMarking L}
  {hz : center (L ⧸ pCore 2 L) = ⊥} {hn : InitialNatural h e hz}
  {d : Replacement L R} (s : FullSymmetricAction h e hz hn d)

include s in
/-- The original restriction preserves the critical moving commutator and
identifies it with the full predecessor-radius intersection commutator. -/
theorem critical_radius_exact_moving_actor
    (hc : DistanceTwo.CentralLayer d) (hb : 2 < replacementDistance h d)
    {a a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a a')
    (hforward : 4 ≤ (Q d.radical a').relIndex (Z d.radical a)) :
    ∃ W : Subgroup (FreeAmalgam d.radical), W ≤ U d.radical a' ∧
      W.relIndex (U d.radical a') ≤ 2 ∧
      2 ≤ (Q d.radical a).relIndex W ∧
      ⁅W,Z d.radical a⁆ = ⁅U d.radical a',Z d.radical a⁆ ∧
      ⁅V d.radical a ⊓ Q d.radical (p.walk.getVert (p.walk.length-2)),W⁆ =
        ⁅U d.radical a',Z d.radical a⁆ := by
  have hl : 2 < p.walk.length := by rw [p.length_eq_b]; exact hb
  let t := p.walk.getVert (p.walk.length-1)
  have hct : Adjacent d.radical a' t := by
    have hh := p.walk.adj_getVert_succ (i:=p.walk.length-1) (by omega)
    rw [show p.walk.length-1+1=p.walk.length by omega,p.walk.getVert_length] at hh
    exact adjacent_symm d.radical ((cosetGraph_adj d.radical _ _).mp hh)
  have ht : color d.radical t = true := by
    have hh := adjacent_color_ne d.radical hct
    rw [p.end_color] at hh
    cases he : color d.radical t <;> simp_all
  have het : Adjacent d.radical (p.walk.getVert (p.walk.length-2)) t := by
    have hh := p.walk.adj_getVert_succ (i:=p.walk.length-2) (by omega)
    rw [show p.walk.length-2+1=p.walk.length-1 by omega] at hh
    exact (cosetGraph_adj d.radical _ _).mp hh
  let Y := V d.radical a ⊓ Q d.radical (p.walk.getVert (p.walk.length-2))
  have hYt : Y ≤ Q d.radical t := inf_le_right.trans (Q_le_adjacent_h d.radical ht het)
  have hY : Y ≤ stabilizer d.radical a' := fun _ hx =>
    (hYt hx).2 _ (adjacent_symm d.radical hct)
  have hcomm : ⁅U d.radical a',Z d.radical a⁆ ≤ ⁅Z d.radical a,Z d.radical a'⁆ := by
    rw [commutator_comm]
    exact commutator_mono le_rfl (DistanceEight.U_le_Z d.radical a')
  have hRZa : ⁅Z d.radical a,Z d.radical a'⁆ ≤ Z d.radical a :=
    ((critical_Z_commutator_le_moving (h:=h) p).trans inf_le_left).trans (DistanceEight.U_le_Z d.radical a)
  let := (replacementGeometry h d).Z_elementary (replacementDistance_pos h d) a p.start_color
  have hAA : ⁅U d.radical a',Z d.radical a⁆ ≤
      centralizer (Z d.radical a : Set (FreeAmalgam d.radical)) :=
    (hcomm.trans hRZa).trans (le_centralizer_iff_isMulCommutative.mpr inferInstance)
  have hAY : ⁅U d.radical a',Z d.radical a⁆ ≤ centralizer (Y : Set (FreeAmalgam d.radical)) :=
    hcomm.trans (le_centralizer_iff.mp (critical_radius_intersection_centralizes (h:=h) p hb))
  obtain ⟨i,hi,hir,hiQ,hiU⟩ := vertex_coordinates (h:=h) hc a' p.end_color
  have hA : Z d.radical a ≤ i.range := by
    rw [hir]
    exact Z_le_stabilizer_of_dist_le a _ p.critical.1.le
  obtain ⟨W,hW,hindex,hpres,hcontrol⟩ := embedded_cover_restriction_preserving s i hi (Z d.radical a) hA
    (hiQ.symm ▸ hforward) (hiU.symm ▸ hAA)
  have hWU : W ≤ U d.radical a' := hiU ▸ hW
  have hWi : W.relIndex (U d.radical a') ≤ 2 := hiU ▸ hindex
  have hreverse := reverse_critical_moving_image_four_le s hc p hforward
  let : Finite (U d.radical a') := by
    apply Nat.finite_of_card_ne_zero
    rw [←hiU,card_map_of_injective hi]
    exact Nat.card_pos.ne'
  have hmul := relIndex_inf_mul_relIndex (Q d.radical a) W (U d.radical a')
  rw [inf_eq_left.mpr hWU] at hmul
  have hle : (Q d.radical a).relIndex (U d.radical a') ≤
      (Q d.radical a ⊓ W).relIndex (U d.radical a') :=
    relIndex_le_of_le_left inf_le_left index_ne_zero_of_finite
  have htwo : 2 ≤ (Q d.radical a).relIndex W := by
    rw [←hmul] at hle
    by_contra hn
    have hu : (Q d.radical a).relIndex W ≤ 1 := by omega
    have hh := Nat.mul_le_mul hu hWi
    omega
  refine ⟨W,hWU,hWi,htwo,hiU ▸ hpres,?_⟩
  apply le_antisymm
  · rw [commutator_comm]
    have hh := hcontrol Y (hY.trans_eq hir.symm) (hiU.symm ▸ hAY)
    rw [hiU] at hh
    exact hh
  · have hZaY : Z d.radical a ≤ Y := by
      apply le_inf (Z_le_VBall d.radical a 2)
      apply Z_le_Q_of_dist_lt d.radical a ((replacementGeometry h d).exists_critical a p.start_color)
      rw [(replacementGeometry h d).distance_constant a p.start_color,
        p.dist_start (Nat.sub_le _ _)]
      have hlen : p.walk.length = replacementDistance h d := p.length_eq_b
      change p.walk.length - 2 < replacementDistance h d
      omega
    have hp : ⁅W,Z d.radical a⁆ = ⁅U d.radical a',Z d.radical a⁆ := hiU ▸ hpres
    rw [←hp,commutator_comm W]
    exact commutator_mono hZaY le_rfl

include s in
/-- A large critical image admits a restricted full endpoint seed, including
its entire last-edge attachment. Its commutator with the whole predecessor
radius intersection is exactly the original critical commutator. -/
theorem large_image_full_seed_control
    (hc : DistanceTwo.CentralLayer d) (hb : 2 < replacementDistance h d)
    {a a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a a')
    (hlarge : 4 ≤ (Q d.radical a').relIndex (Z d.radical a)) :
    ∃ E : Subgroup (FreeAmalgam d.radical),
      Z d.radical (p.walk.getVert (p.walk.length-1)) ≤ E ∧ E ≤ Z d.radical a' ∧
      E.relIndex (Z d.radical a') ≤ 2 ∧ 2 ≤ (Q d.radical a).relIndex E ∧
      ⁅Z d.radical a,E⁆ = ⁅Z d.radical a,Z d.radical a'⁆ ∧
      ⁅V d.radical a ⊓ Q d.radical (p.walk.getVert (p.walk.length-2)),E⁆ =
        ⁅Z d.radical a,Z d.radical a'⁆ := by
  let t := p.walk.getVert (p.walk.length-1)
  let Y := V d.radical a ⊓ Q d.radical (p.walk.getVert (p.walk.length-2))
  let F := Z d.radical t
  have hl : 2 < p.walk.length := p.length_eq_b ▸ hb
  have het : Adjacent d.radical a' t := by
    have hh := p.walk.adj_getVert_succ (i := p.walk.length-1) (by omega)
    rw [show p.walk.length-1+1=p.walk.length by omega,p.walk.getVert_length] at hh
    exact adjacent_symm d.radical ((cosetGraph_adj d.radical _ _).mp hh)
  have hct : Adjacent d.radical (p.walk.getVert (p.walk.length-2)) t := by
    have hh := p.walk.adj_getVert_succ (i := p.walk.length-2) (by omega)
    rw [show p.walk.length-2+1=p.walk.length-1 by omega] at hh
    exact (cosetGraph_adj d.radical _ _).mp hh
  have ht : color d.radical t = true := by
    have hh := adjacent_color_ne d.radical het
    rw [p.end_color] at hh
    cases he : color d.radical t <;> simp_all
  have hYQt : Y ≤ Q d.radical t := inf_le_right.trans (Q_le_adjacent_h d.radical ht hct)
  have hFY : F ≤ centralizer (Y : Set (FreeAmalgam d.radical)) := by
    intro z hz y hy
    change z ∈ Z d.radical t at hz
    rw [Z,if_neg (by simp [ht])] at hz
    exact (mem_omegaCenter_iff.mp hz).2.2 y (hYQt hy)
  have haY : Z d.radical a ≤ Y := by
    apply le_inf (Z_le_VBall d.radical a 2)
    apply Z_le_Q_of_dist_lt d.radical a ((replacementGeometry h d).exists_critical a p.start_color)
    rw [(replacementGeometry h d).distance_constant a p.start_color,
      p.dist_start (Nat.sub_le _ _)]
    have hh : p.walk.length = replacementDistance h d := p.length_eq_b
    change p.walk.length-2 < replacementDistance h d
    omega
  have hFZe : F ≤ Z d.radical a' := adjacent_Z_le d.radical p.end_color het
  have hdecomp : Z d.radical a' = U d.radical a' ⊔ F :=
    DistanceTwo.CentralLayer.Z_eq_moving_sup_edge_at h e hz d p.end_color het
  obtain ⟨W,hWU,hWi,hWimage,hpres,hcontrol⟩ := critical_radius_exact_moving_actor s hc hb p hlarge
  let D := ⁅U d.radical a',Z d.radical a⁆
  change ⁅W,Z d.radical a⁆ = D at hpres
  change ⁅Y,W⁆ = D at hcontrol
  have hDZe : D ≤ Z d.radical a' := by
    dsimp only [D]
    rw [commutator_comm]
    exact ((commutator_mono le_rfl (DistanceEight.U_le_Z d.radical a')).trans
      ((critical_Z_commutator_le_moving (h := h) p).trans inf_le_right)).trans
        (DistanceEight.U_le_Z d.radical a')
  let := (replacementGeometry h d).Z_elementary (replacementDistance_pos h d) a' p.end_color
  have hZeN : Z d.radical a' ≤ normalizer (D : Set (FreeAmalgam d.radical)) :=
    ((le_centralizer_iff_isMulCommutative.mpr inferInstance).trans
      (centralizer_le hDZe)).trans (Subgroup.centralizer_le_normalizer _)
  have hfull : ⁅Z d.radical a,Z d.radical a'⁆ = D := by
    apply le_antisymm
    · rw [commutator_comm,hdecomp]
      exact commutator_sup_le_of_relative_normal (Z d.radical a') _ _ _ D hZeN
        (DistanceEight.U_le_Z d.radical a') hFZe le_rfl
        ((commutator_eq_bot_iff_le_centralizer.mpr (hFY.trans (centralizer_le haY))).le.trans bot_le)
    · rw [commutator_comm (Z d.radical a)]
      exact commutator_mono (DistanceEight.U_le_Z d.radical a') le_rfl
  let E := W ⊔ F
  have hWZe : W ≤ Z d.radical a' := hWU.trans (DistanceEight.U_le_Z d.radical a')
  have hEZe : E ≤ Z d.radical a' := sup_le hWZe hFZe
  have hUEn : U d.radical a' ≤ normalizer (E : Set (FreeAmalgam d.radical)) :=
    (DistanceEight.U_le_Z d.radical a').trans
      (((le_centralizer_iff_isMulCommutative.mpr inferInstance).trans
        (centralizer_le hEZe)).trans (Subgroup.centralizer_le_normalizer _))
  have hsup : E ⊔ U d.radical a' = Z d.radical a' := by
    apply le_antisymm (sup_le hEZe (DistanceEight.U_le_Z d.radical a'))
    rw [hdecomp]
    exact sup_le le_sup_right (le_sup_right.trans le_sup_left)
  let := finite_Z d.radical a'
  let : Finite (U d.radical a') := Finite.of_injective
    (inclusion (DistanceEight.U_le_Z d.radical a')) (inclusion_injective _)
  let : Finite E := Finite.of_injective (inclusion hEZe) (inclusion_injective _)
  have hEi : E.relIndex (Z d.radical a') ≤ 2 := by
    let J := E ⊔ U d.radical a'
    let : (E.subgroupOf J).Normal := normal_subgroupOf_of_le_normalizer
      (sup_le E.le_normalizer hUEn)
    have hi := relIndex_sup_left ((U d.radical a').subgroupOf J) (E.subgroupOf J)
    rw [←subgroupOf_sup le_sup_left le_sup_right,relIndex_subgroupOf le_rfl,
      relIndex_subgroupOf le_sup_right] at hi
    rw [←hsup,hi]
    exact (relIndex_le_of_le_left (show W ≤ E from le_sup_left) index_ne_zero_of_finite).trans hWi
  have hEimage : 2 ≤ (Q d.radical a).relIndex E :=
    hWimage.trans (relIndex_le_of_le_right (show W ≤ E from le_sup_left) index_ne_zero_of_finite)
  have hYE : ⁅Y,E⁆ = D := by
    apply le_antisymm
    · rw [commutator_comm]
      exact commutator_sup_le_of_relative_normal (Z d.radical a') W F Y D hZeN hWZe hFZe
        (by rw [commutator_comm]; exact hcontrol.le)
        ((commutator_eq_bot_iff_le_centralizer.mpr hFY).le.trans bot_le)
    · rw [←hcontrol]
      exact commutator_mono le_rfl le_sup_left
  have hZaE : ⁅Z d.radical a,E⁆ = D := by
    apply le_antisymm
    · exact (commutator_mono le_rfl hEZe).trans_eq hfull
    · rw [←hpres,commutator_comm W]
      exact commutator_mono le_rfl le_sup_left
  exact ⟨E,le_sup_right,hEZe,hEi,hEimage,hZaE.trans hfull.symm,hYE.trans hfull.symm⟩
include s in
/-- Restricted-seed normalization for the large-image step of (5.12)(1).
The constructed restriction includes the full central attachment and controls every
backward seed in the starting radius, using the literal midpoint core. -/
theorem large_image_distance_four_kernel_control
    (hc : DistanceTwo.CentralLayer d) (hb : replacementDistance h d = 4)
    {a a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a a')
    (hlarge : 4 ≤ (Q d.radical a').relIndex (Z d.radical a)) :
    ∃ E : Subgroup (FreeAmalgam d.radical),
      Z d.radical (p.walk.getVert 3) ≤ E ∧ E ≤ Z d.radical a' ∧
      E.relIndex (Z d.radical a') ≤ 2 ∧ 2 ≤ (Q d.radical a).relIndex E ∧
      ⁅Z d.radical a,E⁆ = ⁅Z d.radical a,Z d.radical a'⁆ ∧
      ∀ z, (cosetGraph d.radical).dist z a ≤ 2 →
        let K := U d.radical z ⊓ Q d.radical (p.walk.getVert 2)
        ⁅K,E⁆ ≤ ⁅Z d.radical a,Z d.radical a'⁆ ∧
        ⁅K ⊔ Z d.radical a,E⁆ = ⁅Z d.radical a,Z d.radical a'⁆ ∧
        E ≤ normalizer ((K ⊔ Z d.radical a : Subgroup (FreeAmalgam d.radical)) : Set (FreeAmalgam d.radical)) := by
  have hb2 : 2 < replacementDistance h d := by omega
  have hl : p.walk.length = 4 := p.length_eq_b.trans hb
  obtain ⟨E,hFE,hEZ,hEi,hEimage,hZaE,hYE⟩ := large_image_full_seed_control s hc hb2 p hlarge
  rw [hl] at hFE hYE
  refine ⟨E,hFE,hEZ,hEi,hEimage,hZaE,?_⟩
  intro z hz
  let K := U d.radical z ⊓ Q d.radical (p.walk.getVert 2)
  let Y := V d.radical a ⊓ Q d.radical (p.walk.getVert 2)
  have hKV : U d.radical z ≤ V d.radical a :=
    (DistanceEight.U_le_Z d.radical z).trans (le_iSup_of_le z (le_iSup_of_le hz le_rfl))
  have hKY : K ≤ Y := inf_le_inf_right _ hKV
  have hZaY : Z d.radical a ≤ Y := by
    apply le_inf (Z_le_VBall d.radical a 2)
    apply Z_le_Q_of_dist_lt d.radical a ((replacementGeometry h d).exists_critical a p.start_color)
    rw [(replacementGeometry h d).distance_constant a p.start_color,p.dist_start (by omega)]
    exact hb2
  have hKE : ⁅K,E⁆ ≤ ⁅Z d.radical a,Z d.radical a'⁆ :=
    (commutator_mono hKY le_rfl).trans_eq hYE
  have hjoin : ⁅K ⊔ Z d.radical a,E⁆ = ⁅Z d.radical a,Z d.radical a'⁆ :=
    le_antisymm ((commutator_mono (sup_le hKY hZaY) le_rfl).trans_eq hYE)
      (hZaE.ge.trans (commutator_mono (show Z d.radical a ≤ K ⊔ Z d.radical a from le_sup_right) le_rfl))
  have hRZa : ⁅Z d.radical a,Z d.radical a'⁆ ≤ Z d.radical a :=
    ((critical_Z_commutator_le_moving (h := h) p).trans inf_le_left).trans
      (DistanceEight.U_le_Z d.radical a)
  exact ⟨hKE,hjoin,le_normalizer_iff_commutator_le_left.mpr
    (hjoin.le.trans (hRZa.trans le_sup_right))⟩

include e hz hn in
/-- The actual natural replacement supplies a conjugate backward critical
path and its normalized full-seed kernel in the large-image branch.
No point-core image, cover order or universal escape premise is imposed. -/
theorem large_image_selected_backward_kernel_knownSimple
    (hb : replacementDistance h d = 4) {a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) a')
    (hlarge : 4 ≤ (Q d.radical a').relIndex (Z d.radical (alpha d.radical))) :
    ∃ x ∈ stabilizer d.radical (alpha d.radical),
      ∃ q : CriticalPath d.radical (replacementGeometry h d)
          (act d.radical x (p.walk.getVert 2)) (p.walk.getVert 2),
        q.walk.getVert 2 = alpha d.radical ∧
        q.walk.getVert 1 = act d.radical x (p.walk.getVert 1) ∧
        ∃ E : Subgroup (FreeAmalgam d.radical),
          Z d.radical (p.walk.getVert 3) ≤ E ∧ E ≤ Z d.radical a' ∧
          E.relIndex (Z d.radical a') ≤ 2 ∧
          2 ≤ (Q d.radical (alpha d.radical)).relIndex E ∧
          ⁅Z d.radical (alpha d.radical),E⁆ = ⁅Z d.radical (alpha d.radical),Z d.radical a'⁆ ∧
          let K := U d.radical (act d.radical x (p.walk.getVert 2)) ⊓ Q d.radical (p.walk.getVert 2)
          ⁅K,E⁆ ≤ ⁅Z d.radical (alpha d.radical),Z d.radical a'⁆ ∧
          ⁅K ⊔ Z d.radical (alpha d.radical),E⁆ = ⁅Z d.radical (alpha d.radical),Z d.radical a'⁆ ∧
          E ≤ normalizer ((K ⊔ Z d.radical (alpha d.radical) : Subgroup (FreeAmalgam d.radical)) :
            Set (FreeAmalgam d.radical)) := by
  have hb2 : 2 < replacementDistance h d := by omega
  let s := fullSymmetricAction_knownSimple h e hz hn d hb2
  have hc := DistanceTwo.centralLayer_knownSimple G L R h e hz hn d
  have hnon := large_image_selected_span_nonabelian s hc hb p hlarge
  obtain ⟨_,x,hx,q,_,hq2,hq3⟩ := selected_span_conjugate_critical_path (h := h) hb2 p hnon
  let r : CriticalPath d.radical (replacementGeometry h d)
      (act d.radical x (p.walk.getVert 2)) (p.walk.getVert 2) := {
    start_color := q.end_color
    walk := q.walk.reverse
    shortest := by rw [SimpleGraph.Walk.length_reverse,q.shortest,SimpleGraph.dist_comm]
    critical := critical_reverse_pair s hc q }
  have hql : q.walk.length = 4 := q.length_eq_b.trans hb
  have hr2 : r.walk.getVert 2 = alpha d.radical := by
    change q.walk.reverse.getVert 2 = _
    rw [SimpleGraph.Walk.getVert_reverse,hql]
    exact hq2
  have hr1 : r.walk.getVert 1 = act d.radical x (p.walk.getVert 1) := by
    change q.walk.reverse.getVert 1 = _
    rw [SimpleGraph.Walk.getVert_reverse,hql]
    exact hq3
  obtain ⟨E,hFE,hEZ,hEi,hEimage,hZaE,hkernel⟩ :=
    large_image_distance_four_kernel_control s hc hb p hlarge
  refine ⟨x,hx,r,hr2,hr1,E,hFE,hEZ,hEi,hEimage,hZaE,?_⟩
  apply hkernel
  have hd := (r.dist_start (i := 2) (by have hh := r.length_eq_b.trans hb; omega)).le
  simpa only [hr2] using hd


end AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
