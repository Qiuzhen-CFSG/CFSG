module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.OriginalSylow.TerminalKernels
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.OriginalSylow.TerminalKernels
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicBorelThompson
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicSmallBackward
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.SylowKernelPair
import all CFSG.Quasithin.ChapterC.Section01.NaturalSixControl.SymplecticSetup.ForwardKernel
public import Theory.GroupTheory.Commutator.NormalizedIndexTwo

/-!
# The common full kernel on the original Borel edge

A moving small critical line gives two conjugate critical hyperplanes. The
proper Thompson mover normalizes both. Their intersection has index four
in the whole seed, while the entire edge seed has index eight. Quadraticity
places the critical line in that intersection; its noncentrality under the
edge then gives the direct product of the line with the entire edge seed.
The proper mover fixes the intersection and moves the whole seed into it.

On three actual generating backward shifts, the restricted-commutator span
therefore splits as the last critical line times its full edge intersection.
That intersection is central under all three starting stabilizers. It has
index two in the span and contributes no displacement under the last whole
stabilizer. TerminalNormalization uses the common-kernel identity to control
the entire terminal seed, and OriginalSylowExceptional applies the span
identity to the literal original source.

The natural-branch import supplies only two group-theoretic lemmas about
index-two conjugate subgroups and conjugate-orbit fixers, with no graph or
natural-layer hypotheses. All graph subgroups here belong to the original
exceptional amalgam; both moving covers and the odd cubic kernel are retained.

Source: Meierfrankenfeld--Stellmacher, Pushing up weak BN-pairs of rank two
(1993), (5.10), printed p.922. The index-two subgroup calculation also appears
in Natural.Exhaustion.LargeDistance.SectionFive.SylowKernelPair.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender BinaryPermutation
open Theory.SpecificGroups.SymmetricSix Theory.SpecificGroups.SymmetricSix.BinaryFlags
open CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup
open scoped IsMulCommutative commutatorElement Pointwise
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Exceptional.OriginalSylow
open Exhaustion Exhaustion.LargeDistance Exhaustion.LargeDistance.CubicFull
universe u
variable {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
  (h : SmallMSPair KnownSimple.IsKnownSimple L R) (e : CentralMarking L)
  (hz : Nat.card (center (L ⧸ pCore 2 L)) = 3)
  (hk : layerKernel L R = extensionKernel h)
local notation "Rg" => edge L R
local notation "π" => CubicAction.projection h e hz hk

include h e hz hk in
/-- The common full critical kernel on a moving Borel edge is the critical
line joined with the entire edge seed. Its index is four in the whole seed.
The proper mover fixes this kernel and moves the whole seed into it. -/
theorem borel_moving_common_kernel
    (u : S) (hR : (Rg).map π = borel.map (MulAut.conj u).toMonoidHom)
    {a z : Vertex Rg} (p : CriticalPath Rg (sourceGeometry h) a z)
    (hp : (Q Rg z).relIndex (Z Rg a) < 4)
    (hmove : ¬ Q Rg (p.walk.getVert 1) ≤ centralizer
      ((⁅Z Rg a,Z Rg z⁆ : Subgroup (FreeAmalgam Rg)) : Set _)) :
    let t := p.walk.getVert 1
    let T := Q Rg t
    let J := edgeOffenderJoin a t
    let K := Z Rg a ⊓ Q Rg z
    let F := Z Rg a ⊓ centralizer (componentOrbit (Z Rg z) T : Set _)
    let D := ⁅Z Rg a,Z Rg z⁆
    T ⊓ centralizer (D : Set (FreeAmalgam Rg)) = J ∧
      F = ⨅ x : T, K.map (MulAut.conj (x : FreeAmalgam Rg)).toMonoidHom ∧
      F.relIndex (Z Rg a) = 4 ∧ F = D ⊔ Z Rg t ∧ D ⊓ Z Rg t = ⊥ ∧
      J ≤ centralizer (F : Set (FreeAmalgam Rg)) ∧ ⁅Z Rg a,J⁆ ≤ F := by
  let t := p.walk.getVert 1
  let T := Q Rg t
  let J := edgeOffenderJoin a t
  let K := Z Rg a ⊓ Q Rg z
  let F := Z Rg a ⊓ centralizer (componentOrbit (Z Rg z) T : Set _)
  let D := ⁅Z Rg a,Z Rg z⁆
  let C := Z Rg t
  have hb := distance_gt_two h e hz hk
  have hl : 0 < p.walk.length := p.length_eq_b ▸ sourceDistance_pos h
  have hat : Adjacent Rg a t := by
    apply (cosetGraph_adj Rg _ _).mp
    simpa only [SimpleGraph.Walk.getVert_zero] using p.walk.adj_getVert_succ (i := 0) hl
  have ht : color Rg t = true := by
    have hh := adjacent_color_ne Rg hat
    rw [p.start_color] at hh
    cases he : color Rg t <;> simp_all
  have hTG : T ≤ stabilizer Rg a := fun _ hx => hx.2 _ (adjacent_symm Rg hat)
  have hTZ := hTG.trans (Z_normalized Rg a)
  let := finite_stabilizer Rg a
  let : Finite T := Finite.of_injective (inclusion hTG) (inclusion_injective _)
  let := finite_Z Rg a
  let := (sourceGeometry h).Z_elementary (sourceDistance_pos h) a p.start_color
  obtain ⟨J₀,_,hJ₀,hQJ,hJT,hJi,_,_,hquad⟩ :=
    borel_edge_maximal_offenders h e hz hk u hR p.start_color hat
  change J = J₀ at hJ₀
  rw [←hJ₀] at hQJ hJT hJi hquad
  have hTJ : T ≤ normalizer (J : Set (FreeAmalgam Rg)) :=
    (normal_subgroupOf_iff_le_normalizer hJT).mp (normal_of_index_eq_two hJi)
  have hJdata := borel_small_mover_normalizes_critical_kernel h e hz hk u hR p hp
  change J ≤ centralizer (D : Set (FreeAmalgam Rg)) ∧
    J ≤ normalizer (K : Set (FreeAmalgam Rg)) at hJdata
  have hNK := small_critical_kernel_normalizer_eq_line_centralizer h e hz hk p hp
  change stabilizer Rg a ⊓ normalizer (K : Set (FreeAmalgam Rg)) =
    stabilizer Rg a ⊓ centralizer (D : Set (FreeAmalgam Rg)) at hNK
  have heq : T ⊓ centralizer (D : Set (FreeAmalgam Rg)) = J := by
    let N := T ⊓ centralizer (D : Set (FreeAmalgam Rg))
    have hJN : J ≤ N := le_inf hJT hJdata.1
    have hmul := relIndex_mul_relIndex J N T hJN inf_le_left
    rw [hJi] at hmul
    have hn : N.relIndex T ≠ 1 := fun hh => hmove ((relIndex_eq_one.mp hh).trans inf_le_right)
    have hi : J.relIndex N = 1 := by
      rcases Nat.prime_mul_iff.mp (hmul ▸ Nat.prime_two) with hh | hh
      · exact (hn hh.2).elim
      · exact hh.2
    exact le_antisymm (relIndex_eq_one.mp hi) hJN
  obtain ⟨x,hx,hxm⟩ := SetLike.not_le_iff_exists.mp hmove
  have hxn : x ∉ normalizer (K : Set (FreeAmalgam Rg)) := by
    intro hn
    have hh : x ∈ stabilizer Rg a ⊓ normalizer (K : Set (FreeAmalgam Rg)) := ⟨hTG hx,hn⟩
    rw [hNK] at hh
    exact hxm hh.2
  have hki : K.relIndex (Z Rg a) = 2 := by
    rw [show K = Z Rg a ⊓ Q Rg z from rfl,inf_relIndex_left]
    exact (small_critical_indices h e hz hk p hp).1
  have hbound : (normalizer (K : Set (FreeAmalgam Rg))).relIndex T ≤ 2 :=
    (relIndex_le_of_le_left hJdata.2 index_ne_zero_of_finite).trans_eq hJi
  have hpairs := Natural.Exhaustion.LargeDistance.SectionFive.SylowKernelPair.kernel_core_pair
    (Z Rg a) K T inf_le_left hTZ hki hbound x hx hxn
  have hF : F = ⨅ x : T, K.map (MulAut.conj (x : FreeAmalgam Rg)).toMonoidHom := by
    have hh := Natural.Exhaustion.LargeDistance.SectionFive.SylowKernelPair.orbit_fixer
      (Z Rg a) (Z Rg z) T hTZ
    rw [critical_seed_centralizer_intersection h e p] at hh
    exact hh
  have hFi : F.relIndex (Z Rg a) = 4 := by rw [hF,hpairs.1]; exact hpairs.2.2.2
  have hAT : Z Rg z ≤ T := by
    apply Z_le_Q_of_dist_lt Rg z ((sourceGeometry h).exists_critical z p.end_color)
    rw [SimpleGraph.dist_comm,p.dist_end,(sourceGeometry h).distance_constant _ p.end_color]
    change p.walk.length-1 < sourceDistance h
    have hh : p.walk.length = sourceDistance h := p.length_eq_b
    omega
  have hAJ : Z Rg z ≤ J := by
    apply borel_small_commutator_actor_le_mover h e hz hk u hR p.start_color hat _ hAT
    rw [small_critical_moving_commutator_eq h e hz hk p hp,
      small_critical_commutator_card h e hz hk p hp]
  have hEJ : componentOrbit (Z Rg z) T ≤ J := by
    apply iSup_le
    intro y
    exact (map_mono hAJ).trans_eq (mem_normalizer_iff_map_conj_eq.mp (hTJ y.property))
  have hDJ : D ≤ ⁅U Rg a,J⁆ := by
    dsimp only [D]
    rw [←small_critical_moving_commutator_eq h e hz hk p hp]
    exact commutator_mono le_rfl hAJ
  have hDZ : D ≤ Z Rg a := critical_seed_commutator_le h p
  have hDF : D ≤ F := le_inf hDZ
    ((commutator_eq_bot_iff_le_centralizer.mp hquad).trans (centralizer_le hEJ) |>.trans' hDJ)
  have hCT : C ≤ centralizer (T : Set (FreeAmalgam Rg)) := terminal_edge_seed_central ht
  have hCZ : C ≤ Z Rg a := adjacent_Z_le Rg p.start_color hat
  have hCF : C ≤ F := le_inf hCZ (hCT.trans (centralizer_le (hEJ.trans hJT)))
  have hCi : C.relIndex (Z Rg a) = 8 := borel_full_seed_edge_index h e hz hk u hR p.start_color hat
  have hmul := relIndex_mul_relIndex C F (Z Rg a) hCF inf_le_left
  rw [hCi,hFi] at hmul
  have hCFi : C.relIndex F = 2 := by omega
  let : Finite D := Finite.of_injective (inclusion hDZ) (inclusion_injective _)
  let : Finite C := Finite.of_injective (inclusion hCZ) (inclusion_injective _)
  have hcardD : Nat.card D = 2 := small_critical_commutator_card h e hz hk p hp
  have hnot : ¬ D ≤ C := fun hh => hmove (le_centralizer_iff.mp (hh.trans hCT))
  let : Finite (D ⊓ C : Subgroup (FreeAmalgam Rg)) :=
    Finite.of_injective (inclusion inf_le_left) (inclusion_injective _)
  have hDC : D ⊓ C = ⊥ := by
    by_contra hn
    have hpos := (one_lt_card_iff_ne_bot (D ⊓ C : Subgroup (FreeAmalgam Rg))).mpr hn
    have hh : D ⊓ C = D := eq_of_le_of_card_ge inf_le_left (by omega)
    exact hnot (hh ▸ (show D ⊓ C ≤ C from inf_le_right))
  have hCN : C ≤ normalizer (D : Set (FreeAmalgam Rg)) :=
    (hCZ.trans ((le_centralizer (Z Rg a)).trans (centralizer_le hDZ))).trans
      (Subgroup.centralizer_le_normalizer _)
  have hjoini : C.relIndex (D ⊔ C) = 2 := by
    rw [relIndex_sup_of_normalizes D C hCN,←inf_relIndex_right,inf_comm,hDC]
    simpa using hcardD
  have hjoinF : D ⊔ C ≤ F := sup_le hDF hCF
  have hm := relIndex_mul_relIndex C (D ⊔ C) F le_sup_right hjoinF
  rw [hjoini,hCFi] at hm
  have hdecomp : F = D ⊔ C := le_antisymm (relIndex_eq_one.mp (by omega)) hjoinF
  have hJF : J ≤ centralizer (F : Set (FreeAmalgam Rg)) := by
    apply le_centralizer_iff.mp
    rw [hdecomp]
    exact sup_le (le_centralizer_iff.mp hJdata.1) (hCT.trans (centralizer_le hJT))
  refine ⟨heq,hF,hFi,hdecomp,hDC,hJF,?_⟩
  change ⁅Z Rg a,J⁆ ≤ F
  rw [hF]
  apply le_iInf
  intro y
  have hZy : (Z Rg a).map (MulAut.conj (y : FreeAmalgam Rg)).toMonoidHom = Z Rg a :=
    mem_normalizer_iff_map_conj_eq.mp (hTZ y.property)
  have hJy := mem_normalizer_iff_map_conj_eq.mp (hTJ y.property)
  have hKy : K.map (MulAut.conj (y : FreeAmalgam Rg)).toMonoidHom ≤ Z Rg a :=
    (map_mono (show K ≤ Z Rg a from inf_le_left)).trans_eq hZy
  have hJNy : J ≤ normalizer (K.map (MulAut.conj (y : FreeAmalgam Rg)).toMonoidHom : Set _) := by
    rw [←hJy]
    exact (map_mono hJdata.2).trans (K.le_normalizer_map _)
  apply commutator_le_of_normalized_index_two (Z Rg a) _ J hKy _ (hJT.trans hTZ) hJNy
  rw [←hZy,relIndex_map_map_of_injective _ _ (MulAut.conj _).injective]
  exact hki

include h e hz hk in
/-- The actual restricted-commutator span splits as its last critical line
and its full edge intersection. This intersection is central at all three
starts, and the quotient by it has order two. -/
theorem borel_three_shift_kernel_decomposition
    (hb : 4 < sourceDistance h)
    (u : S) (hR : (Rg).map π = borel.map (MulAut.conj u).toMonoidHom)
    {a a' : Vertex Rg} (p : CriticalPath Rg (sourceGeometry h) a a')
    (q : BorelBackwardShift (h := h) p) (r : BorelBackwardShift (h := h) q.path)
    (t : BorelBackwardShift (h := h) r.path) :
    let z := q.path.walk.getVert (q.path.walk.length-2)
    let v := r.path.walk.getVert (r.path.walk.length-2)
    let H := ⁅Z Rg t.start ⊓ Q Rg v,Z Rg z ⊓ Q Rg r.start⁆
    let D := ⁅Z Rg t.start,Z Rg v⁆
    let I := (H ⊔ D) ⊓ Z Rg t.edge
    H ⊔ D = D ⊔ I ∧ I.relIndex (H ⊔ D) = 2 ∧
      I ≤ centralizer (stabilizer Rg t.start : Set (FreeAmalgam Rg)) ∧
      ∀ Y : Subgroup (FreeAmalgam Rg), Y ≤ stabilizer Rg t.start →
        ⁅H ⊔ D,Y⁆ = ⁅D,Y⁆ := by
  let z := q.path.walk.getVert (q.path.walk.length-2)
  let v := r.path.walk.getVert (r.path.walk.length-2)
  let K := Z Rg t.start ⊓ Q Rg v
  let F := Z Rg z ⊓ Q Rg r.start
  let H := ⁅K,F⁆
  let D := ⁅Z Rg t.start,Z Rg v⁆
  let I := (H ⊔ D) ⊓ Z Rg t.edge
  have ht := two_borel_backward_shifts_small_moving h e hz hk hb q.path r t
  have hsmall : (Q Rg v).relIndex (Z Rg t.start) < 4 := by rw [ht.2.1]; decide
  have hcommon := borel_moving_common_kernel h e hz hk u hR t.path hsmall ht.2.2.2.2
  dsimp only at hcommon
  rw [t.first] at hcommon
  have htcol : color Rg t.edge = true := by
    have hh := adjacent_color_ne Rg t.adjacent_start
    rw [r.path.start_color] at hh
    cases he : color Rg t.edge <;> simp_all
  have hzv : (cosetGraph Rg).dist z v = 2 := by
    rw [SimpleGraph.dist_comm,r.path.dist_end]
    have hl : r.path.walk.length = sourceDistance h := r.path.length_eq_b
    omega
  have hFT : F ≤ Q Rg t.edge := inf_le_right.trans
    (Q_le_adjacent_h Rg htcol t.adjacent_start)
  have hFv : F ≤ Q Rg v := inf_le_left.trans (Z_le_Q_of_dist_lt Rg z
    ((sourceGeometry h).exists_critical z r.path.end_color) (by
      rw [(sourceGeometry h).distance_constant z r.path.end_color,hzv]
      change 2 < sourceDistance h
      omega))
  have hDv : D ≤ Z Rg v := by
    dsimp only [D]
    rw [commutator_comm]
    exact le_normalizer_iff_commutator_le_left.mp
      ((Z_le_stabilizer_of_dist_le t.start _ t.path.critical.1.le).trans (Z_normalized Rg v))
  have hFcent : F ≤ centralizer (D : Set (FreeAmalgam Rg)) :=
    hFv.trans ((le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp
      (Z_centralizes_Q Rg v t.path.end_color))).trans (centralizer_le hDv))
  have hFJ : F ≤ edgeOffenderJoin t.start t.edge := (le_inf hFT hFcent).trans_eq hcommon.1
  have hHcommon := (commutator_mono (show K ≤ Z Rg t.start from inf_le_left) hFJ).trans
    hcommon.2.2.2.2.2.2
  have hspan : H ⊔ D ≤ D ⊔ Z Rg t.edge := sup_le
    (hHcommon.trans_eq hcommon.2.2.2.1) le_sup_left
  have hcentral := borel_three_shift_kernel_intersection_central h e hz hk hb u hR p q r t
  have hIt : I ≤ centralizer (stabilizer Rg t.start : Set (FreeAmalgam Rg)) :=
    hcentral.2.2.2.2.1.le.trans inf_le_right
  let := (sourceGeometry h).Z_elementary (sourceDistance_pos h) t.start t.path.start_color
  have hCN : Z Rg t.edge ≤ normalizer (D : Set (FreeAmalgam Rg)) :=
    ((adjacent_Z_le Rg t.path.start_color t.adjacent_shift).trans
      ((le_centralizer (Z Rg t.start)).trans
        (centralizer_le (critical_seed_commutator_le h t.path)))).trans
          (Subgroup.centralizer_le_normalizer _)
  have hdecomp : H ⊔ D = D ⊔ I := by
    apply le_antisymm _ (sup_le le_sup_right inf_le_left)
    intro x hx
    have hxprod : x ∈ (D : Set (FreeAmalgam Rg)) * (Z Rg t.edge : Set (FreeAmalgam Rg)) := by
      rw [←coe_mul_of_right_le_normalizer_left D (Z Rg t.edge) hCN]
      exact hspan hx
    obtain ⟨d,hd,c,hc,hdc⟩ := hxprod
    have hcspan : c ∈ H ⊔ D := by
      have he : c = d⁻¹*x := by rw [←hdc]; simp
      rw [he]
      exact (H ⊔ D).mul_mem ((H ⊔ D).inv_mem (mem_sup_right hd)) hx
    rw [←hdc]
    exact (D ⊔ I).mul_mem (mem_sup_left hd) (mem_sup_right ⟨hcspan,hc⟩)
  have hIN : I ≤ normalizer (D : Set (FreeAmalgam Rg)) := inf_le_right.trans hCN
  let := finite_Z Rg t.start
  let : Finite I := Finite.of_injective
    (inclusion (inf_le_left.trans hcentral.2.1)) (inclusion_injective _)
  have hindex : I.relIndex (H ⊔ D) = 2 := by
    rw [hdecomp,relIndex_sup_of_normalizes D I hIN,←inf_relIndex_right,inf_comm,hcentral.2.2.2.2.2]
    simpa using ht.2.2.2.1
  refine ⟨hdecomp,hindex,hIt,?_⟩
  intro Y hY
  change ⁅H ⊔ D,Y⁆ = ⁅D,Y⁆
  rw [hdecomp]
  exact commutator_sup_fixed D I Y hIN (hIt.trans (centralizer_le hY))

end AlternatingSixReconstruction.Exceptional.OriginalSylow
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
