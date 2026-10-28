module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicPlanePairedFixedSeeds
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicPlanePairedFixedSeeds
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicPlaneKernels
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicPlaneBackward
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicPlaneCriticalPlane

/-!
# Common full kernels on the paired cubic paths

On the retained paths a--v--c--t--z and b--v'--c'--t'--z, set
F = Z_z intersect Q_a, F' = Z_z intersect Q_b and I = F intersect F'.
The original critical line T = [Z_a,Z_z] supplements F' in Z_z and lies
in F. Consequently F = I times T, with trivial factor intersection,
[F : I] = 2 and [Z_z : I] = 4 (indices in the usual larger/smaller order).

The radius Y = V_a intersect Q_c centralizes T. Thus [Y,I] = [Y,F] is
the same nonzero radius line H. Its alignment with T modulo the full
endpoint center, and the fact that this center fixes Z_b, show that H
is disjoint from F'. This does not identify H with T.

It follows that N_Y(I) = C_Y(I). The previously computed forward action
kernel identifies this subgroup with the first-edge orbit joined with
Y intersect Q_z, of index two in Y. The fixed subgroup in I is precisely
F' intersect Z_t. A radius element outside the normalizer moves I to a
second subgroup whose join with I is F and whose intersection with I is
F' intersect Z_t. The index argument takes place inside the finite full
seed; all its central attachments remain present.

The same conclusions hold on the opposite retained path. The applications
preserve the original conjugator, exact cross-distances, generating edge,
larger opposite-kernel commutator, cubic projection with kernel E and
nontrivial odd E/Q, both covers of orders sixteen and thirty-two, and the
original proper odd-index radical. These calculations do not yet exclude
the paired configuration. The terminal contradiction, other image/distance/
Borel branches, both core exhaustions and unconditional reconstruction
remain required. Internal imports reuse existing private subgroup and
conjugation calculations without changing their public boundaries.

Source: Meierfrankenfeld--Stellmacher, Pushing up weak BN-pairs of rank two
(1993), (3.3)(ii) and the paired comparisons in (5.12)(1),(3), printed
pp.866--867,924--927; Aschbacher--Smith C.1.31--32, printed pp.135--136.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open Theory.SpecificGroups.SymmetricSix Theory.SpecificGroups.SymmetricSix.BinaryFlags
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
open scoped Pointwise IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicFull
universe u
variable {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
  (h : SmallMSPair KnownSimple.IsKnownSimple L R) (e : CentralMarking L)
  (hz : Nat.card (center (L ⧸ pCore 2 L)) = 3)
  (hk : layerKernel L R = extensionKernel h)
local notation "Rg" => edge L R
local notation "π" => CubicAction.projection h e hz hk

private theorem common_kernel_supplement {J : Type*} [Group J]
    (Z F F' T : Subgroup J) [IsMulCommutative Z]
    (hF : F ≤ Z) (hF' : F' ≤ Z) (hT : T ≤ F) (hs : F' ⊔ T = Z) :
    (F ⊓ F') ⊔ T = F := by
  have hn : T ≤ normalizer (F' : Set J) :=
    (((hT.trans hF).trans (le_centralizer (H := Z))).trans
      (centralizer_le hF')).trans (Subgroup.centralizer_le_normalizer _)
  apply le_antisymm (sup_le inf_le_left hT)
  intro x hx
  have hm : x ∈ (F' : Set J) * (T : Set J) := by
    rw [←coe_mul_of_right_le_normalizer_left F' T hn,hs]
    exact hF hx
  obtain ⟨b,hb,t,ht,rfl⟩ := hm
  have hbF : b ∈ F := by
    simpa only [mul_inv_cancel_right] using F.mul_mem hx (F.inv_mem (hT ht))
  exact mul_mem_sup ⟨hbF,hb⟩ ht

include h e hz hk in
/-- The common full kernel retains the radius line. Its normalizer inside
that radius equals its centralizer and has index two. -/
theorem plane_radius_common_kernel_control
    (u : S) (hR : (Rg).map π = D.map (MulAut.conj u).toMonoidHom)
    (hb4 : sourceDistance h = 4)
    (hsmall : ∀ a z (_p : CriticalPath Rg (sourceGeometry h) a z),
      (Q Rg z).relIndex (Z Rg a) < 4)
    {a b z : Vertex Rg} (p : CriticalPath Rg (sourceGeometry h) a z)
    (q : CriticalPath Rg (sourceGeometry h) b z)
    (hescape : ¬ ⁅V Rg a ⊓ Q Rg (p.walk.getVert 2),Z Rg z⁆ ≤ Z Rg a)
    (hsupp : (Z Rg z ⊓ Q Rg b) ⊔ ⁅Z Rg a,Z Rg z⁆ = Z Rg z)
    (hdis : ⁅Z Rg a,Z Rg z⁆ ⊓ (Z Rg z ⊓ Q Rg b) = ⊥) :
    let Y := V Rg a ⊓ Q Rg (p.walk.getVert 2)
    let F := Z Rg z ⊓ Q Rg a
    let F' := Z Rg z ⊓ Q Rg b
    let I := F ⊓ F'
    let T := ⁅Z Rg a,Z Rg z⁆
    let H := ⁅Y,F⁆
    let K := localZSpan Rg a (p.walk.getVert 1) ⊔ (Y ⊓ Q Rg z)
    I ⊔ T = F ∧ T ⊓ I = ⊥ ∧ I.relIndex F = 2 ∧
      I.relIndex (Z Rg z) = 4 ∧
      ⁅Y,I⁆ = H ∧ Nat.card H = 2 ∧ H ⊓ F' = ⊥ ∧
      I ⊓ centralizer (Y : Set (FreeAmalgam Rg)) = F' ⊓ Z Rg (p.walk.getVert 3) ∧
      (centralizer (Y : Set (FreeAmalgam Rg))).relIndex I = 2 ∧
      Y ⊓ centralizer (I : Set (FreeAmalgam Rg)) = K ∧
      Y ⊓ normalizer (I : Set (FreeAmalgam Rg)) = K ∧ K.relIndex Y = 2 := by
  let Y := V Rg a ⊓ Q Rg (p.walk.getVert 2)
  let F := Z Rg z ⊓ Q Rg a
  let F' := Z Rg z ⊓ Q Rg b
  let I := F ⊓ F'
  let T := ⁅Z Rg a,Z Rg z⁆
  let H := ⁅Y,F⁆
  let C := stabilizer Rg z ⊓ centralizer (stabilizer Rg z : Set (FreeAmalgam Rg))
  have hb := distance_gt_two h e hz hk
  have hl : p.walk.length = 4 := p.length_eq_b.trans hb4
  have hct : Adjacent Rg (p.walk.getVert 2) (p.walk.getVert 3) :=
    (cosetGraph_adj Rg _ _).mp (p.walk.adj_getVert_succ (i := 2) (by omega))
  have hzt : Adjacent Rg z (p.walk.getVert 3) := by
    have hh := p.walk.adj_getVert_succ (i := 3) (by omega)
    rw [show 3+1=p.walk.length by omega,p.walk.getVert_length] at hh
    exact adjacent_symm Rg ((cosetGraph_adj Rg _ _).mp hh)
  have ht : color Rg (p.walk.getVert 3) = true := by
    have hh := adjacent_color_ne Rg hzt
    rw [p.end_color] at hh
    cases he : color Rg (p.walk.getVert 3) <;> simp_all
  have hYt : Y ≤ Q Rg (p.walk.getVert (p.walk.length-1)) := by
    rw [hl]
    exact inf_le_right.trans (Q_le_adjacent_h Rg ht hct)
  have hYG : Y ≤ stabilizer Rg z := by
    have hh : Y ≤ Q Rg (p.walk.getVert 3) := by
      simpa only [hl,Nat.reduceSub] using hYt
    exact hh.trans (fun _ hx => hx.2 _ (adjacent_symm Rg hzt))
  have hTa : T ≤ Z Rg a := le_normalizer_iff_commutator_le_left.mp
    ((critical_Z_le_stabilizer Rg (sourceGeometry h) a p.start_color
      (by rw [(sourceGeometry h).distance_constant _ p.start_color]; exact sourceDistance_pos h)
      p.critical).trans (Z_normalized Rg a))
  have hTZ : T ≤ Z Rg z := hsupp ▸ le_sup_right
  have hTF : T ≤ F := le_inf hTZ (hTa.trans ((Z_le_VBall Rg _ 2).trans
    ((sourceGeometry h).V_le_Q hb a p.start_color)))
  have hTC : T ≤ centralizer (Y : Set (FreeAmalgam Rg)) :=
    (hTa.trans (commutator_eq_bot_iff_le_centralizer.mp
      (Z_centralizes_Q Rg a p.start_color))).trans
        (centralizer_le (inf_le_left.trans ((sourceGeometry h).V_le_Q hb a p.start_color)))
  let := (sourceGeometry h).Z_elementary (sourceDistance_pos h) z p.end_color
  let := finite_Z Rg z
  have hsplit : I ⊔ T = F := common_kernel_supplement (Z Rg z) F F' T
    inf_le_left inf_le_left hTF hsupp
  have hTI : T ⊓ I = ⊥ := le_bot_iff.mp
    ((inf_le_inf_left T (show I ≤ F' from inf_le_right)).trans_eq hdis)
  have hTcard : Nat.card T = 2 := small_critical_commutator_card h e hz hk p (hsmall _ _ p)
  have hTne : T ≠ ⊥ := by
    intro hh
    rw [hh,card_bot] at hTcard
    omega
  have hFF' : F ≠ F' := by
    intro hh
    exact hTne ((inf_eq_left.mpr (hTF.trans_eq hh)).symm.trans hdis)
  have hFi : F.relIndex (Z Rg z) = 2 := by
    rw [show F = Z Rg z ⊓ Q Rg a from rfl,inf_relIndex_left]
    exact (small_critical_indices h e hz hk p (hsmall _ _ p)).2
  have hF'i : F'.relIndex (Z Rg z) = 2 := by
    rw [show F' = Z Rg z ⊓ Q Rg b from rfl,inf_relIndex_left]
    exact (small_critical_indices h e hz hk q (hsmall _ _ q)).2
  have hIi : I.relIndex (Z Rg z) = 4 :=
    intersection_index_four (Z Rg z) F F' inf_le_left inf_le_left hFi hF'i hFF'
  have hIFi : I.relIndex F = 2 := by
    have hm := relIndex_mul_relIndex I F (Z Rg z) inf_le_left inf_le_left
    rw [hFi,hIi] at hm
    omega
  have strip (A : Subgroup (FreeAmalgam Rg)) (hAY : A ≤ Y) : ⁅A,I⁆ = ⁅A,F⁆ := by
    have hTN : T ≤ normalizer (I : Set (FreeAmalgam Rg)) :=
      ((hTZ.trans (le_centralizer (H := Z Rg z))).trans
        (centralizer_le (show I ≤ Z Rg z from inf_le_left.trans inf_le_left))).trans
          (Subgroup.centralizer_le_normalizer _)
    rw [commutator_comm A I,commutator_comm A F,←hsplit]
    exact (commutator_sup_of_central_attachment I T A hTN
      (hTC.trans (centralizer_le hAY))).symm
  have hfixed := plane_radius_paired_fixed_seed h e hz hk u hR hb4 hsmall
    p hescape hsupp hdis
  have hforward := plane_radius_first_edge_action h e hz hk u hR hb4 hsmall p hescape
  have hAY : Z Rg a ≤ Y := (Z_le_localZSpan Rg _ _).trans hforward.1
  have halign := plane_radius_kernel_alignment h e hz hk u hR p (hsmall _ _ p)
    Y inf_le_left hYt hAY hescape
  have hHcard : Nat.card H = 2 := halign.1
  have hHZ : H ≤ Z Rg z := (commutator_mono le_rfl inf_le_left).trans
    (le_normalizer_iff_commutator_le_right.mp (hYG.trans (Z_normalized Rg z)))
  have hCF' : C ≤ centralizer (Z Rg b : Set (FreeAmalgam Rg)) :=
    inf_le_right.trans (centralizer_le (Z_le_stabilizer_of_dist_le b _ q.critical.1.le))
  let qr := CriticalPath.ofPair (geometry := sourceGeometry h) q.end_color
    (critical_reverse Rg (sourceGeometry h) (sourceEdgeCentralizer h e)
      b q.start_color (by
        rw [(sourceGeometry h).distance_constant _ q.start_color]
        exact sourceDistance_pos h) z q.end_color q.critical)
  have hF'fixed : Z Rg z ⊓ centralizer (Z Rg b : Set (FreeAmalgam Rg)) = F' :=
    critical_seed_centralizer_intersection h e qr
  have hHnot : ¬ H ≤ F' := by
    intro hh
    have hHC : H ≤ centralizer (Z Rg b : Set (FreeAmalgam Rg)) :=
      hh.trans (hF'fixed ▸ inf_le_right)
    have hTC' : T ≤ centralizer (Z Rg b : Set (FreeAmalgam Rg)) :=
      (show T ≤ H ⊔ C from halign.2.2.2.2.2 ▸ le_sup_left).trans (sup_le hHC hCF')
    have hTF' : T ≤ F' := hF'fixed ▸ le_inf hTZ hTC'
    exact hTne ((inf_eq_left.mpr hTF').symm.trans hdis)
  let : Finite H := Nat.finite_of_card_ne_zero (by rw [hHcard]; decide)
  let : Finite (H ⊓ F' : Subgroup (FreeAmalgam Rg)) :=
    Finite.of_injective (inclusion inf_le_left) (inclusion_injective _)
  have hHF' : H ⊓ F' = ⊥ := by
    by_contra hn
    have hlo := (one_lt_card_iff_ne_bot (H ⊓ F')).mpr hn
    have he : H ⊓ F' = H := eq_of_le_of_card_ge inf_le_left (by omega)
    exact hHnot (he ▸ inf_le_right)
  have hfixI : I ⊓ centralizer (Y : Set (FreeAmalgam Rg)) =
      F' ⊓ Z Rg (p.walk.getVert 3) := by
    rw [show I = F ⊓ F' from rfl,inf_comm F F',inf_assoc,hfixed.2.1]
  have hidxI : (centralizer (Y : Set (FreeAmalgam Rg))).relIndex I = 2 := by
    let : IsElementaryAbelian 2 F := IsElementaryAbelian.of_le (show F ≤ Z Rg z from inf_le_left)
    exact (fixed_supplement_relIndex Y I T F hsplit hTC).trans hfixed.2.2.1
  have hcentral : Y ⊓ centralizer (I : Set (FreeAmalgam Rg)) =
      Y ⊓ centralizer (F : Set (FreeAmalgam Rg)) := by
    apply le_antisymm
    · apply le_inf inf_le_left
      apply commutator_eq_bot_iff_le_centralizer.mp
      rw [←strip _ inf_le_left]
      exact commutator_eq_bot_iff_le_centralizer.mpr inf_le_right
    · exact inf_le_inf_left _ (centralizer_le (show I ≤ F from inf_le_left))
  have hnormal : Y ⊓ normalizer (I : Set (FreeAmalgam Rg)) =
      Y ⊓ centralizer (I : Set (FreeAmalgam Rg)) := by
    apply le_antisymm
    · apply le_inf inf_le_left
      apply commutator_eq_bot_iff_le_centralizer.mp
      apply le_bot_iff.mp
      have hH : ⁅Y ⊓ normalizer (I : Set (FreeAmalgam Rg)),I⁆ ≤ H :=
        (commutator_mono inf_le_left le_rfl).trans_eq (strip Y le_rfl)
      have hI : ⁅Y ⊓ normalizer (I : Set (FreeAmalgam Rg)),I⁆ ≤ I :=
        le_normalizer_iff_commutator_le_right.mp inf_le_right
      exact (le_inf hH (hI.trans inf_le_right)).trans_eq hHF'
    · exact inf_le_inf_left _ (Subgroup.centralizer_le_normalizer _)
  have hK := plane_radius_forward_action_kernel h e hz hk u hR hb4 hsmall p hescape
  exact ⟨hsplit,hTI,hIFi,hIi,strip Y le_rfl,hHcard,hHF',hfixI,hidxI,
    hcentral.trans hK.1,hnormal.trans (hcentral.trans hK.1),hK.1 ▸ hK.2.1⟩

include h e hz hk in
/-- A radius element moves the common kernel to recover the entire own
kernel, with intersection exactly the opposite-kernel part of the last seed. -/
theorem plane_radius_common_kernel_displacement
    (u : S) (hR : (Rg).map π = D.map (MulAut.conj u).toMonoidHom)
    (hb4 : sourceDistance h = 4)
    (hsmall : ∀ a z (_p : CriticalPath Rg (sourceGeometry h) a z),
      (Q Rg z).relIndex (Z Rg a) < 4)
    {a b z : Vertex Rg} (p : CriticalPath Rg (sourceGeometry h) a z)
    (q : CriticalPath Rg (sourceGeometry h) b z)
    (hescape : ¬ ⁅V Rg a ⊓ Q Rg (p.walk.getVert 2),Z Rg z⁆ ≤ Z Rg a)
    (hsupp : (Z Rg z ⊓ Q Rg b) ⊔ ⁅Z Rg a,Z Rg z⁆ = Z Rg z)
    (hdis : ⁅Z Rg a,Z Rg z⁆ ⊓ (Z Rg z ⊓ Q Rg b) = ⊥) :
    let Y := V Rg a ⊓ Q Rg (p.walk.getVert 2)
    let F := Z Rg z ⊓ Q Rg a
    let F' := Z Rg z ⊓ Q Rg b
    let I := F ⊓ F'
    ∃ y ∈ Y, ¬ I.map (MulAut.conj y).toMonoidHom ≤ I ∧
      I ⊔ I.map (MulAut.conj y).toMonoidHom = F ∧
      I ⊓ I.map (MulAut.conj y).toMonoidHom = F' ⊓ Z Rg (p.walk.getVert 3) := by
  let Y := V Rg a ⊓ Q Rg (p.walk.getVert 2)
  let F := Z Rg z ⊓ Q Rg a
  let F' := Z Rg z ⊓ Q Rg b
  let I := F ⊓ F'
  let E := I ⊓ centralizer (Y : Set (FreeAmalgam Rg))
  obtain ⟨_,_,hIF,hIZ,_,_,_,hE,hEI,hC,hN,hKi⟩ :=
    plane_radius_common_kernel_control h e hz hk u hR hb4 hsmall p q hescape hsupp hdis
  have hn : ¬ Y ≤ normalizer (I : Set (FreeAmalgam Rg)) := by
    intro hn
    have hh := relIndex_eq_one.mpr (hN ▸ le_inf le_rfl hn)
    rw [hKi] at hh
    omega
  obtain ⟨y,hy,hyn⟩ := SetLike.not_le_iff_exists.mp hn
  let f := (MulAut.conj y).toMonoidHom
  let I' := I.map f
  have hl : p.walk.length = 4 := p.length_eq_b.trans hb4
  have hct : Adjacent Rg (p.walk.getVert 2) (p.walk.getVert 3) :=
    (cosetGraph_adj Rg _ _).mp (p.walk.adj_getVert_succ (i := 2) (by omega))
  have hzt : Adjacent Rg z (p.walk.getVert 3) := by
    have hh := p.walk.adj_getVert_succ (i := 3) (by omega)
    rw [show 3+1=p.walk.length by omega,p.walk.getVert_length] at hh
    exact adjacent_symm Rg ((cosetGraph_adj Rg _ _).mp hh)
  have ht : color Rg (p.walk.getVert 3) = true := by
    have hh := adjacent_color_ne Rg hzt
    rw [p.end_color] at hh
    cases he : color Rg (p.walk.getVert 3) <;> simp_all
  have hYG : Y ≤ stabilizer Rg z :=
    (inf_le_right.trans (Q_le_adjacent_h Rg ht hct)).trans
      (fun _ hx => hx.2 _ (adjacent_symm Rg hzt))
  have hYQ : Y ≤ Q Rg a := inf_le_left.trans
    ((sourceGeometry h).V_le_Q (distance_gt_two h e hz hk) a p.start_color)
  have hYN : Y ≤ normalizer (F : Set (FreeAmalgam Rg)) :=
    (le_inf (hYG.trans (Z_normalized Rg z)) (hYQ.trans (Q Rg a).le_normalizer)).trans
      inf_normalizer_le_normalizer_inf
  have hFm : F.map f = F := mem_normalizer_iff_map_conj_eq.mp (hYN hy)
  have hI'F : I' ≤ F := (map_mono (show I ≤ F from inf_le_left)).trans_eq hFm
  let := finite_Z Rg z
  let : Finite F := Finite.of_injective (inclusion inf_le_left) (inclusion_injective _)
  let : Finite I := Finite.of_injective (inclusion inf_le_left) (inclusion_injective _)
  let : Finite I' := Finite.of_injective (inclusion hI'F) (inclusion_injective _)
  have hnot : ¬ I' ≤ I := by
    intro hh
    apply hyn
    apply mem_normalizer_iff_map_conj_eq.mpr
    exact eq_of_le_of_card_ge hh (by
      change Nat.card I ≤ Nat.card (I.map f)
      rw [card_map_of_injective (MulAut.conj y).injective])
  have hI'idx : I'.relIndex F = 2 := by
    conv_lhs => rw [←hFm]
    rw [show I' = I.map f from rfl,relIndex_map_map_of_injective _ _ (MulAut.conj y).injective]
    exact hIF
  have hjoin : I ⊔ I' = F := by
    obtain ⟨x,hx,hxI⟩ := SetLike.not_le_iff_exists.mp hnot
    have hh := sup_zpowers_eq_of_relIndex_prime (show I ≤ F from inf_le_left)
      Nat.prime_two hIF (hI'F hx) hxI
    exact le_antisymm (sup_le inf_le_left hI'F)
      (hh.symm.le.trans (sup_le_sup_left (zpowers_le.mpr hx) _))
  have hmeet : (I ⊓ I').relIndex F = 4 :=
    intersection_index_four F I I' inf_le_left hI'F hIF hI'idx
      (fun hh => hnot hh.symm.le)
  have hEmeet : E ≤ I ⊓ I' := by
    apply le_inf inf_le_left
    intro x hx
    refine ⟨x,hx.1,?_⟩
    exact mul_inv_eq_iff_eq_mul.mpr (hx.2 y hy)
  have hEF : E.relIndex F = 4 := by
    have hm := relIndex_mul_relIndex E I F inf_le_left inf_le_left
    have he : E.relIndex I = 2 := by
      rw [show E = I ⊓ centralizer (Y : Set (FreeAmalgam Rg)) from rfl,inf_relIndex_left]
      exact hEI
    rw [he,hIF] at hm
    exact hm.symm
  have hEq : I ⊓ I' = E := by
    have hm := relIndex_mul_relIndex E (I ⊓ I') F hEmeet (inf_le_left.trans inf_le_left)
    rw [hmeet,hEF] at hm
    exact le_antisymm (relIndex_eq_one.mp (by omega)) hEmeet
  exact ⟨y,hy,hnot,hjoin,hEq.trans hE⟩

include h e hz hk in
/-- Both retained radii act nontrivially on the same common full kernel.
Its normalizer equals its centralizer inside each radius, with index two.
Each radius displaces the common kernel to recover its own full kernel. -/
theorem plane_small_four_paired_common_kernel_control
    (u : S) (hR : (Rg).map π = D.map (MulAut.conj u).toMonoidHom)
    (hb4 : sourceDistance h = 4)
    (hsmall : ∀ a z (_p : CriticalPath Rg (sourceGeometry h) a z),
      (Q Rg z).relIndex (Z Rg a) < 4) :
    ∃ a z, ∃ p : CriticalPath Rg (sourceGeometry h) a z,
      ∃ s, Adjacent Rg z s ∧
        Q Rg s ⊔ (V Rg a ⊓ Q Rg (p.walk.getVert 2)) = stabilizer Rg z ∧
        ∃ g ∈ Q Rg s, act Rg g⁻¹ z = z ∧
          ∃ q : CriticalPath Rg (sourceGeometry h) (act Rg g⁻¹ a) z,
            (∀ i, q.walk.getVert i = act Rg g⁻¹ (p.walk.getVert i)) ∧
            (∀ i j, (cosetGraph Rg).dist (p.walk.getVert i) (q.walk.getVert j) =
              (4-i) + (4-j)) ∧
            let Y := V Rg a ⊓ Q Rg (p.walk.getVert 2)
            let F := Z Rg z ⊓ Q Rg a
            let H := ⁅Y,F⁆
            let C := ⁅Y,Z Rg z⁆
            let common := fun b (r : CriticalPath Rg (sourceGeometry h) b z) b' =>
              let Y₀ := V Rg b ⊓ Q Rg (r.walk.getVert 2)
              let F₀ := Z Rg z ⊓ Q Rg b
              let F₁ := Z Rg z ⊓ Q Rg b'
              let I := F₀ ⊓ F₁
              let T := ⁅Z Rg b,Z Rg z⁆
              let H₀ := ⁅Y₀,F₀⁆
              let K := localZSpan Rg b (r.walk.getVert 1) ⊔ (Y₀ ⊓ Q Rg z)
              (I ⊔ T = F₀ ∧ T ⊓ I = ⊥ ∧ I.relIndex F₀ = 2 ∧
                I.relIndex (Z Rg z) = 4 ∧
                ⁅Y₀,I⁆ = H₀ ∧ Nat.card H₀ = 2 ∧ H₀ ⊓ F₁ = ⊥ ∧
                I ⊓ centralizer (Y₀ : Set (FreeAmalgam Rg)) = F₁ ⊓ Z Rg (r.walk.getVert 3) ∧
                (centralizer (Y₀ : Set (FreeAmalgam Rg))).relIndex I = 2 ∧
                Y₀ ⊓ centralizer (I : Set (FreeAmalgam Rg)) = K ∧
                Y₀ ⊓ normalizer (I : Set (FreeAmalgam Rg)) = K ∧ K.relIndex Y₀ = 2) ∧
                ∃ y ∈ Y₀, ¬ I.map (MulAut.conj y).toMonoidHom ≤ I ∧
                  I ⊔ I.map (MulAut.conj y).toMonoidHom = F₀ ∧
                  I ⊓ I.map (MulAut.conj y).toMonoidHom = F₁ ⊓ Z Rg (r.walk.getVert 3)
            Nat.card H = 2 ∧ H < C ∧ 4 ≤ Nat.card C ∧
              ⁅Y,Z Rg z ⊓ Q Rg (act Rg g⁻¹ a)⁆ = C ∧
              common a p (act Rg g⁻¹ a) ∧ common (act Rg g⁻¹ a) q a := by
  obtain ⟨a,z,p,s,hzs,hgen,g,hg,hfix,q,hverts,hgeom,
    hsupp,hdis,_,hopp,_,_,_,hcard,hstrict,hbig,hescape,_,_⟩ :=
    plane_small_four_full_kernel_comparison h e hz hk u hR hb4 hsmall
  let F := Z Rg z ⊓ Q Rg a
  let F' := Z Rg z ⊓ Q Rg (act Rg g⁻¹ a)
  let f := (MulAut.conj g).toMonoidHom
  have hZz : (Z Rg z).map f = Z Rg z := by
    simpa only [inv_inv,hfix] using (Z_act Rg g⁻¹ z).symm
  have hF : F.map f = F' := by
    rw [show F = Z Rg z ⊓ Q Rg a from rfl,
      Subgroup.map_inf _ _ f (MulAut.conj g).injective,hZz]
    simp only [F',Q_act,inv_inv,f]
  have hFF : (F.map f).map f = F :=
    map_conj_twice_of_square_centralizes F g
      (centralizer_le inf_le_left
        (plane_edge_square_centralizes_seed h e hz hk u hR p.end_color hzs g hg))
  have hsupp' : F ⊔ ⁅Z Rg (act Rg g⁻¹ a),Z Rg z⁆ = Z Rg z := by
    have hh := congrArg (Subgroup.map f) hsupp
    change (F' ⊔ ⁅Z Rg a,Z Rg z⁆).map f = (Z Rg z).map f at hh
    rw [Subgroup.map_sup,←hF,hFF,map_commutator,hZz] at hh
    simpa only [Z_act,inv_inv,f] using hh
  have hdis' : ⁅Z Rg (act Rg g⁻¹ a),Z Rg z⁆ ⊓ F = ⊥ := by
    have hh := congrArg (Subgroup.map f) hdis
    change (⁅Z Rg a,Z Rg z⁆ ⊓ F').map f = (⊥ : Subgroup (FreeAmalgam Rg)).map f at hh
    rw [Subgroup.map_inf _ _ f (MulAut.conj g).injective,←hF,hFF,
      map_commutator,hZz,Subgroup.map_bot] at hh
    simpa only [Z_act,inv_inv,f] using hh
  have hescape' : ¬ ⁅V Rg (act Rg g⁻¹ a) ⊓ Q Rg (q.walk.getVert 2),Z Rg z⁆ ≤
      Z Rg (act Rg g⁻¹ a) := by
    intro hh
    apply hescape
    apply (map_le_map_iff_of_injective (f := f) (MulAut.conj g).injective).mp
    rw [map_commutator,hZz,Subgroup.map_inf _ _ f (MulAut.conj g).injective]
    simpa only [hverts 2,V_act,Q_act,Z_act,inv_inv,f] using hh
  exact ⟨a,z,p,s,hzs,hgen,g,hg,hfix,q,hverts,hgeom,hcard,hstrict,hbig,hopp,
    ⟨plane_radius_common_kernel_control h e hz hk u hR hb4 hsmall p q hescape hsupp hdis,
      plane_radius_common_kernel_displacement h e hz hk u hR hb4 hsmall p q hescape hsupp hdis⟩,
    ⟨plane_radius_common_kernel_control h e hz hk u hR hb4 hsmall q p hescape' hsupp' hdis',
      plane_radius_common_kernel_displacement h e hz hk u hR hb4 hsmall q p hescape' hsupp' hdis'⟩⟩

omit hk in
include h e hz in
/-- Whole-core application of both common-kernel displacement calculations,
retaining the original projection, central attachments and both covers. -/
theorem coreExhaustion_or_cubic_paired_common_kernel_control :
    CoreExhaustion L R ∨
    ∃ hk : layerKernel L R = extensionKernel h,
      Function.Surjective (CubicAction.projection h e hz hk) ∧
      2 < sourceDistance h ∧
      (∀ a : Vertex Rg, color Rg a = false →
        Nat.card (U Rg a) = 16 ∨ Nat.card (U Rg a) = 32) ∧
      ∃ u : S,
        (Rg).map (CubicAction.projection h e hz hk) =
          borel.map (MulAut.conj u).toMonoidHom ∨
        ((Rg).map (CubicAction.projection h e hz hk) =
          D.map (MulAut.conj u).toMonoidHom ∧
        (sourceDistance h = 4 →
          (∀ a z (_p : CriticalPath Rg (sourceGeometry h) a z),
            (Q Rg z).relIndex (Z Rg a) < 4) →
    ∃ a z, ∃ p : CriticalPath Rg (sourceGeometry h) a z,
      ∃ s, Adjacent Rg z s ∧
        Q Rg s ⊔ (V Rg a ⊓ Q Rg (p.walk.getVert 2)) = stabilizer Rg z ∧
        ∃ g ∈ Q Rg s, act Rg g⁻¹ z = z ∧
          ∃ q : CriticalPath Rg (sourceGeometry h) (act Rg g⁻¹ a) z,
            (∀ i, q.walk.getVert i = act Rg g⁻¹ (p.walk.getVert i)) ∧
            (∀ i j, (cosetGraph Rg).dist (p.walk.getVert i) (q.walk.getVert j) =
              (4-i) + (4-j)) ∧
            let Y := V Rg a ⊓ Q Rg (p.walk.getVert 2)
            let F := Z Rg z ⊓ Q Rg a
            let H := ⁅Y,F⁆
            let C := ⁅Y,Z Rg z⁆
            let common := fun b (r : CriticalPath Rg (sourceGeometry h) b z) b' =>
              let Y₀ := V Rg b ⊓ Q Rg (r.walk.getVert 2)
              let F₀ := Z Rg z ⊓ Q Rg b
              let F₁ := Z Rg z ⊓ Q Rg b'
              let I := F₀ ⊓ F₁
              let T := ⁅Z Rg b,Z Rg z⁆
              let H₀ := ⁅Y₀,F₀⁆
              let K := localZSpan Rg b (r.walk.getVert 1) ⊔ (Y₀ ⊓ Q Rg z)
              (I ⊔ T = F₀ ∧ T ⊓ I = ⊥ ∧ I.relIndex F₀ = 2 ∧
                I.relIndex (Z Rg z) = 4 ∧
                ⁅Y₀,I⁆ = H₀ ∧ Nat.card H₀ = 2 ∧ H₀ ⊓ F₁ = ⊥ ∧
                I ⊓ centralizer (Y₀ : Set (FreeAmalgam Rg)) = F₁ ⊓ Z Rg (r.walk.getVert 3) ∧
                (centralizer (Y₀ : Set (FreeAmalgam Rg))).relIndex I = 2 ∧
                Y₀ ⊓ centralizer (I : Set (FreeAmalgam Rg)) = K ∧
                Y₀ ⊓ normalizer (I : Set (FreeAmalgam Rg)) = K ∧ K.relIndex Y₀ = 2) ∧
                ∃ y ∈ Y₀, ¬ I.map (MulAut.conj y).toMonoidHom ≤ I ∧
                  I ⊔ I.map (MulAut.conj y).toMonoidHom = F₀ ∧
                  I ⊓ I.map (MulAut.conj y).toMonoidHom = F₁ ⊓ Z Rg (r.walk.getVert 3)
            Nat.card H = 2 ∧ H < C ∧ 4 ≤ Nat.card C ∧
              ⁅Y,Z Rg z ⊓ Q Rg (act Rg g⁻¹ a)⁆ = C ∧
              common a p (act Rg g⁻¹ a) ∧ common (act Rg g⁻¹ a) q a)) := by
  rcases coreExhaustion_or_cubic_plane_paths h e hz with
    hex | ⟨hk,hs,hb,hcovers,u,hborel | ⟨hplane,_⟩⟩
  · exact Or.inl hex
  · exact Or.inr ⟨hk,hs,hb,hcovers,u,Or.inl hborel⟩
  · exact Or.inr ⟨hk,hs,hb,hcovers,u,Or.inr ⟨hplane,
      fun hb4 hsmall => plane_small_four_paired_common_kernel_control h e hz hk u hplane hb4 hsmall⟩⟩

omit hk in
include h e hz in
/-- Literal C.1.32 application, retaining the original radical, odd extension
kernel quotient, full central attachments and both common-kernel displacement calculations. -/
theorem rankTwo_or_cubic_paired_common_kernel_control :
    RankTwoAlternatives L R ∨
    ∃ hk : layerKernel L R = extensionKernel h,
      Function.Surjective (CubicAction.projection h e hz hk) ∧
      2 < sourceDistance h ∧
      (∀ a : Vertex Rg, color Rg a = false →
        Nat.card (U Rg a) = 16 ∨ Nat.card (U Rg a) = 32) ∧
      ∃ u : S,
        (Rg).map (CubicAction.projection h e hz hk) =
          borel.map (MulAut.conj u).toMonoidHom ∨
        ((Rg).map (CubicAction.projection h e hz hk) =
          D.map (MulAut.conj u).toMonoidHom ∧
        (sourceDistance h = 4 →
          (∀ a z (_p : CriticalPath Rg (sourceGeometry h) a z),
            (Q Rg z).relIndex (Z Rg a) < 4) →
    ∃ a z, ∃ p : CriticalPath Rg (sourceGeometry h) a z,
      ∃ s, Adjacent Rg z s ∧
        Q Rg s ⊔ (V Rg a ⊓ Q Rg (p.walk.getVert 2)) = stabilizer Rg z ∧
        ∃ g ∈ Q Rg s, act Rg g⁻¹ z = z ∧
          ∃ q : CriticalPath Rg (sourceGeometry h) (act Rg g⁻¹ a) z,
            (∀ i, q.walk.getVert i = act Rg g⁻¹ (p.walk.getVert i)) ∧
            (∀ i j, (cosetGraph Rg).dist (p.walk.getVert i) (q.walk.getVert j) =
              (4-i) + (4-j)) ∧
            let Y := V Rg a ⊓ Q Rg (p.walk.getVert 2)
            let F := Z Rg z ⊓ Q Rg a
            let H := ⁅Y,F⁆
            let C := ⁅Y,Z Rg z⁆
            let common := fun b (r : CriticalPath Rg (sourceGeometry h) b z) b' =>
              let Y₀ := V Rg b ⊓ Q Rg (r.walk.getVert 2)
              let F₀ := Z Rg z ⊓ Q Rg b
              let F₁ := Z Rg z ⊓ Q Rg b'
              let I := F₀ ⊓ F₁
              let T := ⁅Z Rg b,Z Rg z⁆
              let H₀ := ⁅Y₀,F₀⁆
              let K := localZSpan Rg b (r.walk.getVert 1) ⊔ (Y₀ ⊓ Q Rg z)
              (I ⊔ T = F₀ ∧ T ⊓ I = ⊥ ∧ I.relIndex F₀ = 2 ∧
                I.relIndex (Z Rg z) = 4 ∧
                ⁅Y₀,I⁆ = H₀ ∧ Nat.card H₀ = 2 ∧ H₀ ⊓ F₁ = ⊥ ∧
                I ⊓ centralizer (Y₀ : Set (FreeAmalgam Rg)) = F₁ ⊓ Z Rg (r.walk.getVert 3) ∧
                (centralizer (Y₀ : Set (FreeAmalgam Rg))).relIndex I = 2 ∧
                Y₀ ⊓ centralizer (I : Set (FreeAmalgam Rg)) = K ∧
                Y₀ ⊓ normalizer (I : Set (FreeAmalgam Rg)) = K ∧ K.relIndex Y₀ = 2) ∧
                ∃ y ∈ Y₀, ¬ I.map (MulAut.conj y).toMonoidHom ≤ I ∧
                  I ⊔ I.map (MulAut.conj y).toMonoidHom = F₀ ∧
                  I ⊓ I.map (MulAut.conj y).toMonoidHom = F₁ ⊓ Z Rg (r.walk.getVert 3)
            Nat.card H = 2 ∧ H < C ∧ 4 ≤ Nat.card C ∧
              ⁅Y,Z Rg z ⊓ Q Rg (act Rg g⁻¹ a)⁆ = C ∧
              common a p (act Rg g⁻¹ a) ∧ common (act Rg g⁻¹ a) q a)) :=
  (coreExhaustion_or_cubic_paired_common_kernel_control h e hz).imp
    (rankTwo_of_exhaustion h e hz) id

end AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicFull
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
