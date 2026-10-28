module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicForwardSelectors
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicSelectedFour

/-!
# Excluding the cubic point-core image

Retain the critical paths a--z and d--c, with midpoints c and a, the
original generating edge, and the same element of G_a carrying c to d.
For a prospective two-edge extension v--t--d with
Q_t join Z_c = G_d, the comparison

  [U_v intersect Q_a, X_c] <= [Z_d,Z_c]

holds before v--a is known critical. If Z_v is not contained in Q_a,
minimality constructs that critical path and the established three-path
comparison applies. Otherwise U_v intersect Q_a = U_v. The abelian
point-core edge image makes Q_t normalize its commutator with X_c intersect
Q_d. If nonzero, this is the original order-two reverse-kernel line.
Generation makes it central in G_d, contradicting the preceding-selector
kernel theorem. Thus the kernel commutator vanishes in either case.

The comparison places U_v intersect Q_a in the actual Baumann slice B_d,
so the full moving index is at most two. Transport the original strict
local pair to d and a generating edge, using explicit vertex and neighbor
conjugators. Its strict index is preserved and contradicts this bound.
This closes the point-core branch on the original cubic graph, including
the actual b = 4 commutator contradiction; no third critical path or
identification of independently selected paths is assumed.

The whole-core and literal C.1.32 applications now retain only the plane
and borel images. They preserve the actual projection with kernel E, its
nontrivial odd quotient E/Q, the original radical, and both 16/32 moving
covers. Those two image exclusions, natural exhaustion and both final
reconstruction outcomes remain necessary.

Source: Meierfrankenfeld--Stellmacher, Pushing up weak BN-pairs of rank two
(1993), (5.5)--(5.6), (5.12)(1) and its reselection, pp.915--919,924--925;
Aschbacher--Smith C.1.31--32, pp.135--136.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender BinaryPermutation
open scoped IsMulCommutative commutatorElement Pointwise
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
open CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup
open CFSG.Quasithin.ChapterB.Offenders CFSG.Quasithin.ChapterB.Offenders.Six
open Theory.SpecificGroups.SymmetricSix Theory.SpecificGroups.SymmetricSix.BinaryFlags
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicFull

universe u
variable {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
  (h : SmallMSPair KnownSimple.IsKnownSimple L R) (e : CentralMarking L)
  (hz : Nat.card (center (L ⧸ pCore 2 L)) = 3)
  (hk : layerKernel L R = extensionKernel h)
local notation "Rg" => edge L R
local notation "M" => (L ⊔ R : Subgroup G)
local notation "K" => L.subgroupOf M
local notation "W" => (⁅centralOmega L R,L.subgroupOf (L ⊔ R)⁆ : Subgroup M)
local notation "π" => CubicAction.projection h e hz hk

include h e hz hk in
/-- Full-X control on a prospective extension, without a third critical-path premise. -/
theorem point_selected_precritical_full_omega_control
    (u : S) (hR : (Rg).map π ≤ pointCore.map (MulAut.conj u).toMonoidHom)
    {z c d v t : Vertex Rg}
    (p : CriticalPath Rg (sourceGeometry h) (alpha Rg) z)
    (q : CriticalPath Rg (sourceGeometry h) d c)
    (hpc : p.walk.getVert 2 = c) (hqa : q.walk.getVert 2 = alpha Rg)
    (hgen : Q Rg (q.walk.getVert 1) ⊔ Z Rg z = stabilizer Rg (alpha Rg))
    (g : FreeAmalgam Rg) (hg : g ∈ stabilizer Rg (alpha Rg))
    (hgc : act Rg g c = d)
    (hdt : Adjacent Rg d t) (hvt : Adjacent Rg v t)
    (hgent : Q Rg t ⊔ Z Rg c = stabilizer Rg d) :
    ⁅U Rg v ⊓ Q Rg (alpha Rg),X Rg c ⊓ Q Rg d⁆ = ⊥ ∧
      ⁅U Rg v ⊓ Q Rg (alpha Rg),X Rg c⁆ ≤ ⁅Z Rg d,Z Rg c⁆ := by
  have hb := point_image_distance_eq_four h e hz hk u hR
  have hl : q.walk.length = 4 := q.length_eq_b.trans hb
  have ht : color Rg t = true := by
    have hh := adjacent_color_ne Rg hdt
    rw [q.start_color] at hh
    cases he : color Rg t <;> simp_all
  have hv : color Rg v = false := by
    have hh := adjacent_color_ne Rg hvt
    rw [ht] at hh
    cases he : color Rg v <;> simp_all
  have hvd : (cosetGraph Rg).dist v d ≤ 2 := by
    have h1 := SimpleGraph.dist_eq_one_iff_adj.mpr ((cosetGraph_adj Rg _ _).mpr hvt)
    have h2 := SimpleGraph.dist_eq_one_iff_adj.mpr
      ((cosetGraph_adj Rg _ _).mpr (adjacent_symm Rg hdt))
    simpa only [h1,h2] using (cosetGraph_connected Rg).dist_triangle
      (u := v) (v := t) (w := d)
  by_cases hbad : Z Rg v ≤ Q Rg (alpha Rg)
  · let Y := U Rg v ⊓ Q Rg (alpha Rg)
    let K₀ := X Rg c ⊓ Q Rg d
    let J := ⁅Y,K₀⁆
    let H₀ := ⁅Z Rg c ⊓ Q Rg d,Q Rg (alpha Rg)⁆
    have hY : Y = U Rg v := inf_eq_left.mpr ((DistanceEight.U_le_Z Rg v).trans hbad)
    have hK : K₀ ≤ Q Rg t := inf_le_right.trans (Q_le_adjacent_h Rg ht hdt)
    have htG : Q Rg t ≤ stabilizer Rg v := fun _ hx => hx.2 _ (adjacent_symm Rg hvt)
    have hnorm : Q Rg t ≤ normalizer (J : Set (FreeAmalgam Rg)) := by
      change Q Rg t ≤ normalizer ((⁅Y,K₀⁆ : Subgroup (FreeAmalgam Rg)) : Set _)
      rw [hY,commutator_comm]
      apply fixed_mod_central_normalizes_line K₀ (U Rg v) (Q Rg t)
        (hK.trans (htG.trans (U_normalized v))) (htG.trans (U_normalized v))
      have hab : ⁅(Rg).map π,(Rg).map π⁆ = ⊥ := by
        let := pointCore_elementary
        let : IsElementaryAbelian 2 (pointCore.map (MulAut.conj u).toMonoidHom) := IsElementaryAbelian.map _
        exact commutator_eq_bot_iff_le_centralizer.mpr
          (hR.trans ((le_centralizer_iff_isMulCommutative.mpr inferInstance).trans (centralizer_le hR)))
      exact ((commutator_mono le_rfl hK).trans
        (edge_derived_le_core_of_abelian_image h e hz hk hab hv hvt)).trans
          ((le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp
            (Z_centralizes_Q Rg v hv))).trans (centralizer_le (DistanceEight.U_le_Z Rg v)))
    have hplace := point_shifted_omega_kernel_placement h e hz hk u hR q hv hvd
    rw [hqa] at hplace
    have hJH : J ≤ H₀ := by
      change ⁅Y,X Rg c ⊓ Q Rg d⁆ ≤ H₀
      rw [point_omega_eq_seed h e hz hk u hR c q.end_color,commutator_comm]
      exact commutator_mono le_rfl inf_le_right
    have hHcard : Nat.card H₀ = 2 := by
      simpa only [hqa] using (point_critical_radius_cross_kernel_line_at h e hz hk u hR q).1
    have hzero : J = ⊥ := by
      by_contra hn
      let : Finite H₀ := Nat.finite_of_card_ne_zero (by omega)
      let : Finite J := Finite.of_injective (inclusion hJH) (inclusion_injective _)
      have he : J = H₀ := eq_of_le_of_card_ge hJH (by
        have hh := (one_lt_card_iff_ne_bot J).mpr hn
        omega)
      have hcard : Nat.card J = 2 := he ▸ hHcard
      have htC : Q Rg t ≤ centralizer (J : Set (FreeAmalgam Rg)) :=
        hnorm.trans (normalizer_le_centralizer_of_card_two J hcard)
      have hJZ : J ≤ Z Rg c :=
        (hplace.1.trans (inf_le_right.trans inf_le_left)).trans (DistanceEight.U_le_Z Rg c)
      let := (sourceGeometry h).Z_elementary (sourceDistance_pos h) c q.end_color
      have hcC : Z Rg c ≤ centralizer (J : Set (FreeAmalgam Rg)) :=
        (le_centralizer_iff_isMulCommutative.mpr inferInstance).trans (centralizer_le hJZ)
      have hcentral : H₀ ≤ centralizer (stabilizer Rg d : Set (FreeAmalgam Rg)) := by
        rw [←he]
        apply le_centralizer_iff.mp
        rw [←hgent]
        exact sup_le htC hcC
      exact point_selected_backward_kernel_not_central h e hz hk u hR p q
        hpc hqa hgen g hg hgc hcentral
    refine ⟨hzero,?_⟩
    apply small_critical_omega_kernel_control h e hz hk q (by
      rw [(point_image_critical_indices_two h e hz hk u hR q).1]; decide) Y
    · exact inf_le_right.trans (Q_le_stabilizer_of_dist_le_two (alpha Rg) c rfl q.end_color (by
        rw [←hqa,q.dist_end,hl]))
    · exact commutator_eq_bot_iff_le_centralizer.mp hzero
  · let w : (cosetGraph Rg).Walk v d :=
      .cons ((cosetGraph_adj Rg _ _).mpr hvt)
        (.cons ((cosetGraph_adj Rg _ _).mpr (adjacent_symm Rg hdt)) .nil)
    have hw : w.length = 2 := rfl
    have hn : ¬ Z Rg v ≤ Q Rg (q.walk.getVert (q.walk.length-2)) := by
      rwa [hl,show 4-2=2 from rfl,hqa]
    let r := q.prepend_two (show 2 ≤ (sourceGeometry h).b Rg from by change 2 ≤ sourceDistance h; omega) hv w hw hn
    have hr1 : r.walk.getVert 1 = t := by
      simp only [r,CriticalPath.prepend_two_walk,SimpleGraph.Walk.getVert_append,
        hw,show 1<2 from by decide,ite_true,w,SimpleGraph.Walk.getVert_cons_succ,
        SimpleGraph.Walk.getVert_zero]
    have hr2 : r.walk.getVert 2 = d := by
      simpa only [Nat.zero_add,SimpleGraph.Walk.getVert_zero] using
        q.prepend_two_overlap _ hv w hw hn (i := 0) (Nat.zero_le _)
    have hr : ∃ r : CriticalPath Rg (sourceGeometry h) v (alpha Rg),
        r.walk.getVert 1 = t ∧ r.walk.getVert 2 = d := by
      have hh : ∃ r : CriticalPath Rg (sourceGeometry h) v
          (q.walk.getVert (q.walk.length-2)), r.walk.getVert 1 = t ∧ r.walk.getVert 2 = d :=
        ⟨r,hr1,hr2⟩
      rwa [hl,show 4-2=2 from rfl,hqa] at hh
    obtain ⟨r,hr1,hr2⟩ := hr
    exact point_selected_backward_full_omega_control h e hz hk u hR p q r
      hpc hqa hr2 hgen (by rwa [hr1]) g hg hgc

include h e hz hk in
/-- Every prospective moving cover at a generating edge has Baumann index at most two. -/
theorem point_selected_precritical_slice_le_two
    (u : S) (hR : (Rg).map π ≤ pointCore.map (MulAut.conj u).toMonoidHom)
    {z c d v t : Vertex Rg}
    (p : CriticalPath Rg (sourceGeometry h) (alpha Rg) z)
    (q : CriticalPath Rg (sourceGeometry h) d c)
    (hpc : p.walk.getVert 2 = c) (hqa : q.walk.getVert 2 = alpha Rg)
    (hgen : Q Rg (q.walk.getVert 1) ⊔ Z Rg z = stabilizer Rg (alpha Rg))
    (g : FreeAmalgam Rg) (hg : g ∈ stabilizer Rg (alpha Rg))
    (hgc : act Rg g c = d)
    (hdt : Adjacent Rg d t) (hvt : Adjacent Rg v t)
    (hgent : Q Rg t ⊔ Z Rg c = stabilizer Rg d) :
    (B Rg d ((sourceGeometry h).Z_normal _)).relIndex (U Rg v) ≤ 2 := by
  let Y := U Rg v ⊓ Q Rg (alpha Rg)
  let T := Y ⊔ Z Rg d
  have hb := point_image_distance_eq_four h e hz hk u hR
  have hl : q.walk.length = 4 := q.length_eq_b.trans hb
  have hv : color Rg v = false := by
    have h1 := adjacent_color_ne Rg hdt
    have h2 := adjacent_color_ne Rg hvt
    rw [q.start_color] at h1
    cases hc : color Rg v <;> cases ht : color Rg t <;> simp_all
  have hvd : (cosetGraph Rg).dist v d ≤ 2 := by
    have h1 := SimpleGraph.dist_eq_one_iff_adj.mpr ((cosetGraph_adj Rg _ _).mpr hvt)
    have h2 := SimpleGraph.dist_eq_one_iff_adj.mpr
      ((cosetGraph_adj Rg _ _).mpr (adjacent_symm Rg hdt))
    simpa only [h1,h2] using (cosetGraph_connected Rg).dist_triangle
      (u := v) (v := t) (w := d)
  let := finite_Z Rg v
  let : Finite (U Rg v) := Finite.of_injective
    (inclusion (DistanceEight.U_le_Z Rg v)) (inclusion_injective _)
  have hprepare : Q Rg t ≤ normalizer (Y : Set (FreeAmalgam Rg)) ∧
      Y.relIndex (U Rg v) ≤ 2 := by
    by_cases hbad : Z Rg v ≤ Q Rg (alpha Rg)
    · have hY : Y = U Rg v := inf_eq_left.mpr ((DistanceEight.U_le_Z Rg v).trans hbad)
      rw [hY,relIndex_self]
      exact ⟨(show Q Rg t ≤ stabilizer Rg v from
        fun _ hx => hx.2 _ (adjacent_symm Rg hvt)).trans (U_normalized v),by decide⟩
    · let w : (cosetGraph Rg).Walk v d :=
        .cons ((cosetGraph_adj Rg _ _).mpr hvt)
          (.cons ((cosetGraph_adj Rg _ _).mpr (adjacent_symm Rg hdt)) .nil)
      have hw : w.length = 2 := rfl
      have hn : ¬ Z Rg v ≤ Q Rg (q.walk.getVert (q.walk.length-2)) := by
        rwa [hl,show 4-2=2 from rfl,hqa]
      let r := q.prepend_two (show 2 ≤ (sourceGeometry h).b Rg from by change 2 ≤ sourceDistance h; omega) hv w hw hn
      have hr1 : r.walk.getVert 1 = t := by
        simp only [r,CriticalPath.prepend_two_walk,SimpleGraph.Walk.getVert_append,
          hw,show 1<2 from by decide,ite_true,w,SimpleGraph.Walk.getVert_cons_succ,
          SimpleGraph.Walk.getVert_zero]
      have hr2 : r.walk.getVert 2 = d := by
        simpa only [Nat.zero_add,SimpleGraph.Walk.getVert_zero] using
          q.prepend_two_overlap _ hv w hw hn (i := 0) (Nat.zero_le _)
      have hr : ∃ r : CriticalPath Rg (sourceGeometry h) v (alpha Rg),
          r.walk.getVert 1 = t ∧ r.walk.getVert 2 = d := by
        have hh : ∃ r : CriticalPath Rg (sourceGeometry h) v
            (q.walk.getVert (q.walk.length-2)), r.walk.getVert 1 = t ∧ r.walk.getVert 2 = d :=
          ⟨r,hr1,hr2⟩
        rwa [hl,show 4-2=2 from rfl,hqa] at hh
      obtain ⟨r,hr1,hr2⟩ := hr
      have hnorm := (point_generating_shifted_kernel_central h e hz hk u hR q r
        hqa hr2 (by rwa [hr1])).1
      rw [hr1] at hnorm
      refine ⟨hnorm,?_⟩
      change (U Rg v ⊓ Q Rg (alpha Rg)).relIndex (U Rg v) ≤ 2
      rw [inf_relIndex_left]
      exact (relIndex_le_of_le_right (DistanceEight.U_le_Z Rg v) index_ne_zero_of_finite).trans_eq
        (point_image_critical_indices_two h e hz hk u hR r).1
  have hcontrol := (point_selected_precritical_full_omega_control h e hz hk u hR p q hpc hqa hgen g hg hgc hdt hvt hgent).2
  have hZG : Z Rg c ≤ stabilizer Rg d := critical_Z_le_stabilizer Rg (sourceGeometry h)
    d q.start_color (by
      rw [(sourceGeometry h).distance_constant _ q.start_color]
      exact sourceDistance_pos h) q.critical
  have hZZ : ⁅Z Rg d,Z Rg c⁆ ≤ Z Rg d :=
    le_normalizer_iff_commutator_le_left.mp (hZG.trans (Z_normalized Rg d))
  have hZX : Z Rg c ≤ X Rg c := (point_omega_eq_seed h e hz hk u hR c q.end_color).symm.le
  have hYcomm : ⁅Y,Z Rg c⁆ ≤ Z Rg d :=
    ((commutator_mono le_rfl hZX).trans hcontrol).trans hZZ
  have hYV : Y ≤ V Rg d := inf_le_left.trans ((DistanceEight.U_le_Z Rg v).trans
    (le_iSup_of_le v (le_iSup_of_le hvd le_rfl)))
  have hTcomm : ⁅T,Z Rg c⁆ ≤ Z Rg d :=
    commutator_sup_le_of_relative_normal (stabilizer Rg d) Y (Z Rg d) (Z Rg c)
      (Z Rg d) (Z_normalized Rg d)
      (hYV.trans ((sourceGeometry h).V_local d q.start_color (by
        rw [(sourceGeometry h).distance_constant _ q.start_color]
        exact distance_gt_two h e hz hk)))
      (Z_le_stabilizer Rg d) hYcomm hZZ
  have hTnormal : stabilizer Rg d ≤ normalizer (T : Set (FreeAmalgam Rg)) := by
    rw [←hgent]
    exact sup_le ((le_inf hprepare.1 ((le_sup_left.trans hgent.le).trans (Z_normalized Rg d))).trans
      (normalizer_inf_normalizer_le_normalizer_sup _ _))
      (le_normalizer_iff_commutator_le_left.mpr (hTcomm.trans le_sup_right))
  let := (sourceGeometry h).Z_elementary (sourceDistance_pos h) c q.end_color
  have hescape : ¬ Z Rg c ≤ Q Rg d := (critical_reverse Rg (sourceGeometry h)
    (sourceEdgeCentralizer h e) d q.start_color (by
      rw [(sourceGeometry h).distance_constant _ q.start_color]; exact sourceDistance_pos h)
    c q.end_color q.critical).2
  have hYB : Y ≤ B Rg d ((sourceGeometry h).Z_normal _) :=
    le_sup_left.trans (normalized_radius_le_slice_of_controlled_actor h e hz
      (distance_gt_two h e hz hk) q.start_color T (Z Rg c)
      (sup_le hYV (Z_le_VBall Rg d 2)) hTnormal hZG
      (IsElementaryAbelian.isPGroup 2 (Z Rg c)) hescape hTcomm)
  exact (relIndex_le_of_le_left hYB index_ne_zero_of_finite).trans hprepare.2

include h e hz hk in
private theorem strict_generating_neighbor
    (u : S) (hR : (Rg).map π ≤ pointCore.map (MulAut.conj u).toMonoidHom)
    {z d c : Vertex Rg} (p : CriticalPath Rg (sourceGeometry h) (alpha Rg) z)
    (hstrict : 2 < (B Rg (alpha Rg) ((sourceGeometry h).Z_normal _)).relIndex
      (U Rg (p.walk.getVert 2)))
    (q : CriticalPath Rg (sourceGeometry h) d c) :
    ∃ v t, Adjacent Rg d t ∧ Adjacent Rg v t ∧
      Q Rg t ⊔ Z Rg c = stabilizer Rg d ∧
      2 < (B Rg d ((sourceGeometry h).Z_normal _)).relIndex (U Rg v) := by
  have hb := distance_gt_two h e hz hk
  have hl : 2 < p.walk.length := p.length_eq_b ▸ hb
  obtain ⟨f,hf⟩ := exists_mVertex_of_color Rg q.start_color
  have hbase : act Rg f⁻¹ d = alpha Rg := by
    rw [hf,act_mVertex,mul_inv_cancel]
    rfl
  have hq : ∃ q₀ : CriticalPath Rg (sourceGeometry h) (alpha Rg) (act Rg f⁻¹ c), True := by
    rw [←hbase]
    exact ⟨q.act f⁻¹,trivial⟩
  obtain ⟨q₀,_⟩ := hq
  obtain ⟨s,has,hgen⟩ := small_image_full_point_generating_neighbor h e hz hk u
    (full_point_image_of_contained h e hz hk u hR) q₀ (by
      rw [(point_image_critical_indices_two h e hz hk u hR q₀).1]; decide)
  have hab : Adjacent Rg (alpha Rg) (p.walk.getVert 1) := by
    simpa only [SimpleGraph.Walk.getVert_zero] using
      (cosetGraph_adj Rg _ _).mp (p.walk.adj_getVert_succ (i := 0) (by omega))
  have hcb : Adjacent Rg (p.walk.getVert 2) (p.walk.getVert 1) :=
    adjacent_symm Rg ((cosetGraph_adj Rg _ _).mp (p.walk.adj_getVert_succ (i := 1) (by omega)))
  obtain ⟨k,hkG,hks⟩ := stabilizer_transitive_neighbors Rg (alpha Rg) hab has
  have hkfix : act Rg k (alpha Rg) = alpha Rg := hkG
  have hidx : 2 < (B Rg (alpha Rg) ((sourceGeometry h).Z_normal _)).relIndex
      (U Rg (act Rg k (p.walk.getVert 2))) := by
    have he := Escape.PairingControl.FirstPairing.B_act (geometry := sourceGeometry h) hb k (alpha Rg) rfl
    rw [hkfix] at he
    rw [U_act,he,relIndex_map_map_of_injective _ _ (MulAut.conj k⁻¹).injective]
    exact hstrict
  have hcancel (v : Vertex Rg) : act Rg f (act Rg f⁻¹ v) = v := by
    rw [←act_mul,inv_mul_cancel,act_one]
  have hfd : act Rg f (alpha Rg) = d := by rw [←hbase,hcancel]
  refine ⟨act Rg f (act Rg k (p.walk.getVert 2)),act Rg f s,?_,?_,?_,?_⟩
  · simpa only [hfd] using (adjacent_act_iff Rg f _ _).mpr has
  · apply (adjacent_act_iff Rg f _ _).mpr
    rw [←hks]
    exact (adjacent_act_iff Rg k _ _).mpr hcb
  · have hh := congrArg (Subgroup.map (MulAut.conj f⁻¹).toMonoidHom) hgen
    rw [Subgroup.map_sup,←Q_act,←Z_act,←stabilizer_act,hcancel,hfd] at hh
    exact hh
  · rw [←hfd,Escape.PairingControl.FirstPairing.B_act (geometry := sourceGeometry h) hb f _ rfl,
      U_act,relIndex_map_map_of_injective _ _ (MulAut.conj f⁻¹).injective]
    exact hidx

include h e hz hk in
/-- The original cubic radical image cannot lie in a conjugate of the point core. -/
theorem point_image_impossible
    (u : S) (hR : (Rg).map π ≤ pointCore.map (MulAut.conj u).toMonoidHom) : False := by
  obtain ⟨z,p,hstrict,hrest⟩ := point_exists_strict_attachment h e hz hk u hR
  obtain ⟨d,t,g,hg,hgc,hat,hdt,hgen,q,hqt,hover⟩ :=
    full_point_backward_step_of_strict_forward h e hz hk u
      (full_point_image_of_contained h e hz hk u hR) p hstrict
  have hl : p.walk.length = 4 := p.length_eq_b.trans (point_image_distance_eq_four h e hz hk u hR)
  have hpc : p.walk.getVert 2 = p.walk.getVert (p.walk.length-2) := by rw [hl]
  have hqa : q.walk.getVert 2 = alpha Rg := by
    simpa only [Nat.zero_add,SimpleGraph.Walk.getVert_zero] using hover 0 (Nat.zero_le _)
  obtain ⟨v,s,hds,hvs,hgens,hindex⟩ := strict_generating_neighbor h e hz hk u hR p hstrict q
  have hbound := point_selected_precritical_slice_le_two h e hz hk u hR p q hpc hqa
    (by rwa [hqt]) g hg (by rwa [←hpc]) hds hvs hgens
  omega

omit hk in
include h e hz in
/-- Whole-core exhaustion leaves only the original plane and borel images.
The point-image exclusion discharges its entire distance-four branch. -/
theorem coreExhaustion_or_cubic_plane_or_borel :
    CoreExhaustion L R ∨ ∃ hk : layerKernel L R = extensionKernel h,
      Function.Surjective (CubicAction.projection h e hz hk) ∧
      2 < sourceDistance h ∧
      (∀ a : Vertex Rg, color Rg a = false →
        Nat.card (U Rg a) = 16 ∨ Nat.card (U Rg a) = 32) ∧
      ∃ u : S,
        (Rg).map (CubicAction.projection h e hz hk) =
          D.map (MulAut.conj u).toMonoidHom ∨
        (Rg).map (CubicAction.projection h e hz hk) =
          borel.map (MulAut.conj u).toMonoidHom := by
  rcases coreExhaustion_or_cubic_radical_cases h e hz with
    hex | ⟨hk,hs,hb,hcovers,u,hpoint | hplane | hborel⟩
  · exact Or.inl hex
  · exact (point_image_impossible h e hz hk u hpoint.2.le).elim
  · exact Or.inr ⟨hk,hs,hb,hcovers,u,Or.inl hplane⟩
  · exact Or.inr ⟨hk,hs,hb,hcovers,u,Or.inr hborel⟩

omit hk in
include h e hz in
/-- Literal C.1.32 application with the cubic point-image branch excluded. -/
theorem rankTwo_or_cubic_plane_or_borel :
    RankTwoAlternatives L R ∨ ∃ hk : layerKernel L R = extensionKernel h,
      Function.Surjective (CubicAction.projection h e hz hk) ∧
      2 < sourceDistance h ∧
      (∀ a : Vertex Rg, color Rg a = false →
        Nat.card (U Rg a) = 16 ∨ Nat.card (U Rg a) = 32) ∧
      ∃ u : S,
        (Rg).map (CubicAction.projection h e hz hk) =
          D.map (MulAut.conj u).toMonoidHom ∨
        (Rg).map (CubicAction.projection h e hz hk) =
          borel.map (MulAut.conj u).toMonoidHom :=
  (coreExhaustion_or_cubic_plane_or_borel h e hz).imp (rankTwo_of_exhaustion h e hz) id

end AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicFull
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
