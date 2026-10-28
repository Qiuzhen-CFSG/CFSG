module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.EndpointAttachment

/-!
# The central attachment forced by a large forward slice

At critical distance four with the literal full point-core image, a forward
Baumann slice larger than two supplies a backward critical path on the same
graph. Its full starting kernel A cannot lie in the original Baumann slice:
the backward critical index is two. Hence its commutator H with the original
reverse kernel is nontrivial and has order two.

The selected first edge normalizes A. Its abelian quotient makes it normalize
H, so it fixes H pointwise. The original critical endpoint also fixes H.
Their proved generation fixes H under the whole starting stabilizer and
places H in the selected edge seed. The full-cover estimate puts H in the
product of the original critical line and the endpoint's central attachment.
The critical line is noncentral at the start, so H is not contained in it.
Consequently that actual attachment has order two and lies in the starting
seed.

The final application constructs the backward path and its generating edge
from the large forward slice. It retains both covers, all literal quotient
maps and the original nonsylow radical. This supplies a concrete remaining
case in the selection argument; it does not eliminate the attachment case
or construct a midpoint-conjugate path with two small slices. The whole-core
estimates and unconditional distance exclusions remain separate obligations
of this module family's assembly owner.

Source: Meierfrankenfeld--Stellmacher, *Pushing up weak BN-pairs of rank two*
(1993), the selected-kernel argument in (5.12)(1)--(3), printed pp.924--927.
The order-32 attachment is retained instead of using the native order-16
fixed-edge commutator containment.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped commutatorElement Pointwise
open Theory.SpecificGroups.SymmetricSix.BinaryFlags
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
open CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive
universe u

variable {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
  {h : SmallMSPair KnownSimple.IsKnownSimple L R} {e : CentralMarking L}
  {hz : center (L ⧸ pCore 2 L) = ⊥} {hn : InitialNatural h e hz}
  {d : Replacement L R} (s : FullSymmetricAction h e hz hn d)


private theorem edge_derived_le_core_of_abelian_image
    (hab : ⁅d.radical.map s.projection,d.radical.map s.projection⁆ = ⊥)
    {a t : Vertex d.radical} (ha : color d.radical a = false)
    (hat : Adjacent d.radical a t) :
    ⁅Q d.radical t,Q d.radical t⁆ ≤ Q d.radical a := by
  have hr : ⁅d.radical,d.radical⁆ ≤ pCore 2 d.overgroup := by
    rw [←s.projection_kernel,←Subgroup.map_eq_bot_iff,map_commutator]
    exact hab
  have hbase : ⁅Q d.radical (beta d.radical),Q d.radical (beta d.radical)⁆ ≤
      Q d.radical (alpha d.radical) := by
    rw [Q_beta,Q_alpha d.radical (replacement_radical_isPGroup h d)
      (replacement_core_le_radical h d),←map_commutator]
    exact map_mono hr
  obtain ⟨g,hg|hg⟩ := (adjacent_iff_exists_common d.radical a t).mp hat
  · rcases hg with ⟨rfl,rfl⟩
    have hh := map_mono (f := (MulAut.conj g⁻¹).toMonoidHom) hbase
    rw [map_commutator,←Q_act,←Q_act] at hh
    simpa only [alpha,beta,act_mVertex,act_hVertex,one_mul] using hh
  · rw [hg.1] at ha
    cases ha

private theorem fixed_mod_central_normalizes_line {H : Type*} [Group H]
    (A Q D : Subgroup H) (hAQ : A ≤ normalizer (Q : Set H))
    (hDQ : D ≤ normalizer (Q : Set H))
    (hDA : ⁅D,A⁆ ≤ centralizer (Q : Set H)) :
    D ≤ normalizer ((⁅A,Q⁆ : Subgroup H) : Set H) := by
  apply le_normalizer_closure_iff.mpr
  rintro d hd _ ⟨a,ha,q,hq,rfl⟩
  have hq' : d*q*d⁻¹ ∈ Q := (mem_normalizer_iff.mp (hDQ hd) q).mp hq
  have hk : ⁅d,a⁆ ∈ centralizer (Q : Set H) := hDA (commutator_mem_commutator hd ha)
  have hcomm : ⁅a,d*q*d⁻¹⁆ ∈ Q :=
    le_normalizer_iff_commutator_le_right.mp hAQ (commutator_mem_commutator ha hq')
  have hzero : ⁅⁅d,a⁆,d*q*d⁻¹⁆ = 1 :=
    commutatorElement_eq_one_iff_mul_comm.mpr (hk _ hq').symm
  rw [conjugate_commutatorElement,show d*a*d⁻¹ = ⁅d,a⁆*a by
    simp [commutatorElement_def,mul_assoc],commutatorElement_mul_left_eq_conj_mul,
    hzero,mul_one,←hk _ hcomm,mul_inv_cancel_right]
  exact commutator_mem_commutator ha hq'


private theorem central_attachment_forced
    {F : Type*} [Group F] (H D C B : Subgroup F) [Finite C]
    (hHD : H ≤ D ⊔ C) (hHB : H ≤ B) (hDB : D ≤ B)
    (hCN : C ≤ normalizer (D : Set F)) (hcard : Nat.card C ≤ 2)
    (hne : ¬ H ≤ D) : C ≤ B ∧ Nat.card C = 2 := by
  obtain ⟨x,hx,hxD⟩ : ∃ x, x ∈ H ∧ x ∉ D := by
    by_contra hno
    apply hne
    intro x hx
    by_contra hxD
    exact hno ⟨x,hx,hxD⟩
  have hprod : x ∈ (D : Set F) * (C : Set F) := by
    rw [←coe_mul_of_right_le_normalizer_left D C hCN]
    exact hHD hx
  obtain ⟨z,hz,c,hc,hzc⟩ := hprod
  change z*c=x at hzc
  have hcB : c ∈ B := by
    have hh := B.mul_mem (B.inv_mem (hDB hz)) (hHB hx)
    rw [←hzc,inv_mul_cancel_left] at hh
    exact hh
  have hcne : c ≠ 1 := by
    intro he
    rw [he,mul_one] at hzc
    exact hxD (hzc ▸ hz)
  let : Finite (C ⊓ B : Subgroup F) := Finite.of_injective
    (inclusion inf_le_left) (inclusion_injective _)
  have hnon : (C ⊓ B : Subgroup F) ≠ ⊥ := by
    intro he
    exact hcne (mem_bot.mp (he ▸ (show c ∈ C ⊓ B from ⟨hc,hcB⟩)))
  have hlo := (one_lt_card_iff_ne_bot (C ⊓ B : Subgroup F)).mpr hnon
  have hup : Nat.card (C ⊓ B : Subgroup F) ≤ Nat.card C := card_le_of_le inf_le_left
  have he : C ⊓ B = C := eq_of_le_of_card_ge inf_le_left (by omega)
  exact ⟨he ▸ (inf_le_right : C ⊓ B ≤ B),by omega⟩

/-- The selected backward kernel exposes the central attachment obstructing
its placement in the starting Baumann slice. -/
theorem backward_kernel_attachment
    (hc : DistanceTwo.CentralLayer d) (hb : replacementDistance h d = 4)
    (u : Equiv.Perm (Fin 6))
    (hfull : d.radical.map s.projection = pointCore.map (MulAut.conj u).toMonoidHom)
    {a' c t : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) a')
    (q : CriticalPath d.radical (replacementGeometry h d) c (p.walk.getVert 2))
    (hat : Adjacent d.radical (alpha d.radical) t)
    (hqt : q.walk.getVert 1 = t) (hqa : q.walk.getVert 2 = alpha d.radical)
    (hgen : Q d.radical t ⊔ Z d.radical a' = stabilizer d.radical (alpha d.radical))
    (hlarge : 2 < (B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _)).relIndex
      (U d.radical c)) :
    let A := Z d.radical c ⊓ Q d.radical (p.walk.getVert 2)
    let K := Z d.radical a' ⊓ Q d.radical (alpha d.radical)
    Nat.card (⁅A,K⁆ : Subgroup (FreeAmalgam d.radical)) = 2 ∧
      ⁅A,K⁆ ≤ Z d.radical t ∧
      ⁅A,K⁆ ≤ centralizer (stabilizer d.radical (alpha d.radical) : Set (FreeAmalgam d.radical)) ∧
      U d.radical a' ⊓ centralizer (stabilizer d.radical a' : Set (FreeAmalgam d.radical)) ≤
        Z d.radical (alpha d.radical) ∧
      Nat.card (U d.radical a' ⊓ centralizer
        (stabilizer d.radical a' : Set (FreeAmalgam d.radical)) : Subgroup (FreeAmalgam d.radical)) = 2 := by
  let A := Z d.radical c ⊓ Q d.radical (p.walk.getVert 2)
  let K := Z d.radical a' ⊓ Q d.radical (alpha d.radical)
  let H := ⁅A,K⁆
  let D := ⁅Z d.radical (alpha d.radical),Z d.radical a'⁆
  let C := U d.radical a' ⊓ centralizer (stabilizer d.radical a' : Set (FreeAmalgam d.radical))
  have hb2 : 2 < replacementDistance h d := by omega
  have hl : p.walk.length = 4 := p.length_eq_b.trans hb
  have hql : q.walk.length = 4 := q.length_eq_b.trans hb
  have hf : d.radical.map (SourceReduction.projection h e hz hn d) =
      pointCore.map (MulAut.conj u).toMonoidHom := by
    rwa [SourceReduction.fullSymmetricAction_projection_unique h e hz hn d s] at hfull
  have hi := (full_point_four_critical_indices_two_knownSimple hb u hf p).1
  have hqi := (full_point_four_critical_indices_two_at_knownSimple hb u hf q).1
  have hab : ⁅d.radical.map s.projection,d.radical.map s.projection⁆ = ⊥ := by
    let := pointCore_elementary
    let : IsElementaryAbelian 2 (pointCore.map (MulAut.conj u).toMonoidHom) := IsElementaryAbelian.map _
    rw [hfull]
    exact commutator_eq_bot_iff_le_centralizer.mpr
      (le_centralizer_iff_isMulCommutative.mpr inferInstance)
  have hAn := (small_critical_end_kernels_normalized_of_abelian_image s hc hab q (by omega)).1
  rw [hqt] at hAn
  have hct : Adjacent d.radical c t := by
    have hh := q.walk.adj_getVert_succ (i := 0) (by omega)
    simpa only [SimpleGraph.Walk.getVert_zero,Nat.zero_add,hqt] using
      (cosetGraph_adj d.radical _ _).mp hh
  have ht : color d.radical t = true := by
    have hh := adjacent_color_ne d.radical hat
    change false ≠ color d.radical t at hh
    cases he : color d.radical t <;> simp_all
  have hZV : Z d.radical c ≤ V d.radical (alpha d.radical) :=
    (Z_le_localZSpan d.radical _ _).trans (localZSpan_le_V d.radical (by
      have hh := (q.dist_start (i := 2) (by omega)).le
      simpa only [hqa] using hh))
  have hAV : A ≤ V d.radical (alpha d.radical) := inf_le_left.trans hZV
  have hApre : A ≤ Q d.radical (p.walk.getVert (p.walk.length-2)) := by
    simpa only [hl,Nat.reduceSub] using (inf_le_right : A ≤ Q d.radical (p.walk.getVert 2))
  have hAB : ¬ A ≤ B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _) := by
    intro he
    let := finite_Z d.radical c
    let : Finite (U d.radical c) := Finite.of_injective
      (inclusion (DistanceEight.U_le_Z d.radical c)) (inclusion_injective _)
    have hh := relIndex_le_of_le_left he
      (index_ne_zero_of_finite (H := A.subgroupOf (Z d.radical c)))
    change _ ≤ (Z d.radical c ⊓ Q d.radical (p.walk.getVert 2)).relIndex (Z d.radical c) at hh
    rw [inf_relIndex_left,hqi] at hh
    exact (Nat.not_le_of_gt hlarge)
      ((relIndex_le_of_le_right (DistanceEight.U_le_Z d.radical c) index_ne_zero_of_finite).trans hh)
  have hcard : Nat.card H = 2 :=
    (common_kernel_span_small_line s hc hb2 u hfull.le p hat hgen A hAV hApre hAn hAB).2
  have hKt : K ≤ Q d.radical t := inf_le_right.trans (Q_le_adjacent_h d.radical ht hat)
  have hHA : H ≤ A := le_normalizer_iff_commutator_le_left.mp (hKt.trans hAn)
  have hDZ : H ≤ Z d.radical a' := by
    have hcol : color d.radical (p.walk.getVert 2) = false :=
      (p.vertex_color (by omega)).mpr (by decide)
    have hdist : (cosetGraph d.radical).dist (p.walk.getVert 2) a' = 2 := by
      rw [p.dist_end,hl]
    exact (commutator_mono le_rfl inf_le_left).trans
      (le_normalizer_iff_commutator_le_right.mp
        (((inf_le_right : A ≤ Q d.radical (p.walk.getVert 2)).trans
          (Q_le_stabilizer_of_dist_two d.radical _ _ hcol hdist)).trans (Z_normalized d.radical a')))
  have hHN : Q d.radical t ≤ normalizer (H : Set (FreeAmalgam d.radical)) := by
    dsimp only [H]
    rw [commutator_comm A K]
    apply fixed_mod_central_normalizes_line K A (Q d.radical t) (hKt.trans hAn) hAn
    exact ((commutator_mono le_rfl hKt).trans
      (edge_derived_le_core_of_abelian_image s hab q.start_color hct)).trans
      ((le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp
        (Z_centralizes_Q d.radical c q.start_color))).trans (centralizer_le inf_le_left))
  have hHCt : H ≤ centralizer (Q d.radical t : Set (FreeAmalgam d.radical)) :=
    le_centralizer_iff.mp (hHN.trans (normalizer_le_centralizer_of_card_two _ hcard))
  have hHC : H ≤ centralizer (stabilizer d.radical (alpha d.radical) : Set (FreeAmalgam d.radical)) := by
    apply le_centralizer_iff.mp
    rw [←hgen]
    apply sup_le (le_centralizer_iff.mp hHCt)
    let := (replacementGeometry h d).Z_elementary (replacementDistance_pos h d) a' p.end_color
    exact le_centralizer_iff.mp (hDZ.trans (le_centralizer_iff_isMulCommutative.mpr inferInstance))
  have hHt : H ≤ Q d.radical t :=
    (hHA.trans hAV).trans (((replacementGeometry h d).V_le_Q hb2 _ rfl).trans
      (Q_le_adjacent_h d.radical ht hat))
  have hHZt : H ≤ Z d.radical t := by
    let := (replacementGeometry h d).Z_elementary (replacementDistance_pos h d) a' p.end_color
    intro x hx
    rw [Z,if_neg (by simp [ht])]
    exact mem_omegaCenter_iff.mpr ⟨hHt hx,
      elemPow_eq_one_of_isElementaryAbelian x (hDZ hx),hHCt hx⟩
  have hHZ : H ≤ Z d.radical (alpha d.radical) := hHZt.trans (adjacent_Z_le d.radical rfl hat)
  have hHDC : H ≤ D ⊔ C := by
    dsimp only [H]
    rw [commutator_comm A K]
    exact (commutator_mono le_rfl hApre).trans
      (small_critical_kernel_predecessor_le_commutator_sup_attachment s hc hb2 u hfull.le p (by omega))
  have hDB : D ≤ Z d.radical (alpha d.radical) :=
    ((critical_Z_commutator_le_moving (h := h) p).trans inf_le_left).trans
      (DistanceEight.U_le_Z d.radical _)
  have hDGe : D ≤ stabilizer d.radical a' :=
    (((critical_Z_commutator_le_moving (h := h) p).trans inf_le_right).trans
      (DistanceEight.U_le_Z d.radical _)).trans (Z_le_stabilizer d.radical _)
  have hCN : C ≤ normalizer (D : Set (FreeAmalgam d.radical)) :=
    ((inf_le_right : C ≤ centralizer (stabilizer d.radical a' : Set (FreeAmalgam d.radical))).trans
      (centralizer_le hDGe)).trans (Subgroup.centralizer_le_normalizer _)
  have hnot : ¬ H ≤ D := by
    intro he
    have hzero := le_bot_iff.mp ((le_inf he hHC).trans_eq
      (small_critical_commutator_inf_centralizer s hc p (by omega)))
    rw [hzero,card_bot] at hcard
    omega
  let := finite_Z d.radical a'
  let : Finite C := Finite.of_injective
    (inclusion (inf_le_left.trans (DistanceEight.U_le_Z d.radical a'))) (inclusion_injective _)
  have hatt := central_attachment_forced H D C (Z d.radical (alpha d.radical))
    hHDC hHZ hDB hCN (moving_central_attachment_card s hc p.end_color) hnot
  exact ⟨hcard,hHZt,hHC,hatt⟩

/-- In the literal full-point distance-four branch, a large forward slice
forces the endpoint's central attachment of order two into the starting seed.
The backward path and its large slice are constructed on the original graph. -/
theorem full_point_four_large_slice_attachment_knownSimple
    (hb : replacementDistance h d = 4) (u : Equiv.Perm (Fin 6))
    (hfull : d.radical.map (SourceReduction.projection h e hz hn d) =
      pointCore.map (MulAut.conj u).toMonoidHom)
    {a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) a')
    (hlarge : 2 < (B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _)).relIndex
      (U d.radical (p.walk.getVert 2))) :
    U d.radical a' ⊓ centralizer (stabilizer d.radical a' : Set (FreeAmalgam d.radical)) ≤
      Z d.radical (alpha d.radical) ∧
    Nat.card (U d.radical a' ⊓ centralizer
      (stabilizer d.radical a' : Set (FreeAmalgam d.radical)) : Subgroup (FreeAmalgam d.radical)) = 2 := by
  have hb2 : 2 < replacementDistance h d := by omega
  let s := fullSymmetricAction_knownSimple h e hz hn d hb2
  have hc := DistanceTwo.centralLayer_knownSimple G L R h e hz hn d
  have hf : d.radical.map s.projection = pointCore.map (MulAut.conj u).toMonoidHom := by
    rwa [SourceReduction.fullSymmetricAction_projection_unique h e hz hn d s]
  have hl : p.walk.length = 4 := p.length_eq_b.trans hb
  have hdelta : Adjacent d.radical (p.walk.getVert 2) (p.walk.getVert 1) :=
    adjacent_symm d.radical ((cosetGraph_adj d.radical _ _).mp
      (p.walk.adj_getVert_succ (i := 1) (by omega)))
  obtain ⟨t,hat,hgen,g,hg,hgt,q,hq1,hover,hlargeq⟩ :=
    full_point_backward_shift_knownSimple hb2 u hfull p hdelta hlarge
  have he : p.walk.getVert (p.walk.length-2) = p.walk.getVert 2 := by rw [hl]
  let q' : CriticalPath d.radical (replacementGeometry h d)
      (act d.radical g (p.walk.getVert 2)) (p.walk.getVert 2) := {
    start_color := q.start_color
    walk := q.walk.copy rfl he
    shortest := by rw [SimpleGraph.Walk.length_copy,q.shortest,he]
    critical := by simpa only [he] using q.critical }
  have hq1' : q'.walk.getVert 1 = t := by
    change (q.walk.copy rfl he).getVert 1 = t
    rwa [SimpleGraph.Walk.getVert_copy]
  have hq2' : q'.walk.getVert 2 = alpha d.radical := by
    change (q.walk.copy rfl he).getVert 2 = _
    rw [SimpleGraph.Walk.getVert_copy]
    simpa only [Nat.zero_add,SimpleGraph.Walk.getVert_zero] using hover 0 (Nat.zero_le _)
  exact (backward_kernel_attachment s hc hb u hf p q' hat hq1' hq2' hgen hlargeq).2.2.2

end AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
