module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicCommonAttachment
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicSelectedFour

import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicBackwardRigidity

/-!
# Full omega movement under the original midpoint cores

For an original point-branch critical path a--z with midpoint c, put
F = [X_z,Q_c], H = [Z_z intersect Q_a,Q_c], and D = [Z_a,Z_z].
The whole omega displacement F lies in U_z intersect Q_a. Its next
commutator lies in H, and [H,Q_c] = 1. Thus three successive actions of
the whole midpoint core on X_z are trivial. The attachment plane H join D
is a proper subgroup of F, whose order is eight or sixteen.

The abelian point-core image and its fixed critical line give the kernel
containment by the three-subgroups lemma. To prove strict growth, project
the entire moving cover to its actual natural central quotient. Movement
inside the attachment plane would put the actor image in the critical
transposition group, contradicting the proved midpoint-core image orders
four and eight. The projection kernel is still E; its odd quotient E/Q is
retained when comparing images of two-subgroups. No attachment is removed
from the full-cover cardinality calculation.

On the same selected paths a--z and d--c, the two successive commutators
[[X_z,Q_c],Q_c] and [[X_d,Q_a],Q_a] lie in the same shifted kernel line.
The generating edge fixes this line under G_a. The common central four-group
from CubicCommonAttachment is a proper subgroup of [X_d,Q_a]. The whole-core
and literal C.1.32 applications construct these bounds without new premises,
keeping both cover sizes in the other radical-image branches.

These are full-core action bounds. They do not yet prove the distinct
shifted-kernel inequality [U_d intersect Q_c,X_z] in MS93 (5.12)(1), or its
simultaneous selectors and terminal contradiction. The plane/Sylow image
exclusions, natural exhaustion and final reconstruction assembly remain.

Source: Meierfrankenfeld--Stellmacher, Pushing up weak BN-pairs of rank two
(1993), (3.3)(ii), printed pp.866--867, and (5.12), printed pp.924--927;
Aschbacher--Smith C.1.31--32, printed pp.135--136.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender BinaryPermutation
open scoped IsMulCommutative commutatorElement Pointwise
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
open CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup
open Theory.SpecificGroups.SymmetricSix Theory.SpecificGroups.SymmetricSix.BinaryFlags
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicFull
universe u
variable {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
  (h : SmallMSPair KnownSimple.IsKnownSimple L R) (e : CentralMarking L)
  (hz : Nat.card (center (L ⧸ pCore 2 L)) = 3)
  (hk : layerKernel L R = extensionKernel h)
local notation "M" => (L ⊔ R : Subgroup G)
local notation "W" => (⁅centralOmega L R,L.subgroupOf (L ⊔ R)⁆ : Subgroup M)
local instance : IsElementaryAbelian 2 W := IsElementaryAbelian.of_le (commutator_le_left _ _)
local notation "Rg" => edge L R
local notation "π" => CubicAction.projection h e hz hk


include h e hz hk in
/-- The full opposite omega layer is moved into its original critical kernel
by the whole midpoint core. -/
theorem point_full_omega_midpoint_core_movement
    (u : S) (hR : (Rg).map π ≤ pointCore.map (MulAut.conj u).toMonoidHom)
    {a z : Vertex Rg} (p : CriticalPath Rg (sourceGeometry h) a z) :
    let c := p.walk.getVert 2
    let H := ⁅Z Rg z ⊓ Q Rg a,Q Rg c⁆
    ⁅X Rg z,Q Rg c⁆ ≤ U Rg z ⊓ Q Rg a ∧
      ⁅⁅X Rg z,Q Rg c⁆,Q Rg c⁆ ≤ H ∧
      ⁅⁅⁅X Rg z,Q Rg c⁆,Q Rg c⁆,Q Rg c⁆ = ⊥ := by
  let c := p.walk.getVert 2
  let t := p.walk.getVert 3
  have hb := point_image_distance_eq_four h e hz hk u hR
  have hl : p.walk.length = 4 := p.length_eq_b.trans hb
  have hc : color Rg c = false := (p.vertex_color (by omega)).mpr (by decide)
  have hct : Adjacent Rg c t :=
    (cosetGraph_adj Rg _ _).mp (p.walk.adj_getVert_succ (i := 2) (by omega))
  have hzt : Adjacent Rg z t := by
    have hh := p.walk.adj_getVert_succ (i := 3) (by omega)
    rw [show 3+1=p.walk.length by omega,p.walk.getVert_length] at hh
    exact adjacent_symm Rg ((cosetGraph_adj Rg _ _).mp hh)
  have ht : color Rg t = true := by
    have hh := adjacent_color_ne Rg hct
    rw [hc] at hh
    cases he : color Rg t <;> simp_all
  have hQtG : Q Rg t ≤ stabilizer Rg z := fun _ hx => hx.2 z (adjacent_symm Rg hzt)
  have hQcQt : Q Rg c ≤ Q Rg t := Q_le_adjacent_h Rg ht hct
  have hZaQt : Z Rg a ≤ Q Rg t := by
    apply Z_le_Q_of_dist_lt Rg a ((sourceGeometry h).exists_critical a p.start_color)
    rw [(sourceGeometry h).distance_constant _ p.start_color,p.dist_start (by omega)]
    change 3 < sourceDistance h
    omega
  have hab : ⁅(Rg).map π,(Rg).map π⁆ = ⊥ := by
    let := pointCore_elementary
    let : IsElementaryAbelian 2 (pointCore.map (MulAut.conj u).toMonoidHom) := IsElementaryAbelian.map _
    exact commutator_eq_bot_iff_le_centralizer.mpr
      (hR.trans ((le_centralizer_iff_isMulCommutative.mpr inferInstance).trans (centralizer_le hR)))
  let pr : CriticalPath Rg (sourceGeometry h) z a :=
    ⟨p.end_color,p.walk.reverse,
      by rw [SimpleGraph.Walk.length_reverse,p.shortest,SimpleGraph.dist_comm],
      critical_reverse Rg (sourceGeometry h) (sourceEdgeCentralizer h e) a p.start_color
        (by rw [(sourceGeometry h).distance_constant _ p.start_color]; exact sourceDistance_pos h)
        z p.end_color p.critical⟩
  have hpr : pr.walk.getVert 1 = t := by
    change p.walk.reverse.getVert 1 = t
    rw [SimpleGraph.Walk.getVert_reverse,hl]
  have hDnorm := critical_commutator_normalized_first_of_abelian_image h e hz hk hab pr
  rw [hpr,commutator_comm (Z Rg z)] at hDnorm
  have hDfix : ⁅⁅Z Rg a,Z Rg z⁆,Q Rg c⁆ = ⊥ :=
    commutator_eq_bot_iff_le_centralizer.mpr (le_centralizer_iff.mp
      ((hQcQt.trans hDnorm).trans (normalizer_le_centralizer_of_card_two _
        (point_image_critical_indices_two h e hz hk u hR p).2.2)))
  have hXZ : X Rg z = Z Rg z := point_omega_eq_seed h e hz hk u hR z p.end_color
  have hcom : ⁅⁅Z Rg z,Q Rg c⁆,Z Rg a⁆ = ⊥ := by
    apply commutator_commutator_eq_bot_of_rotate
    · apply commutator_eq_bot_iff_le_centralizer.mpr
      exact ((commutator_mono hQcQt hZaQt).trans
        (edge_derived_le_core_of_abelian_image h e hz hk hab p.end_color hzt)).trans
          (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp
            (Z_centralizes_Q Rg z p.end_color)))
    · exact hDfix
  have hWZ : ⁅Z Rg z,Q Rg c⁆ ≤ Z Rg z := le_normalizer_iff_commutator_le_left.mp
    ((hQcQt.trans hQtG).trans (Z_normalized Rg z))
  have hWK : ⁅X Rg z,Q Rg c⁆ ≤ Z Rg z ⊓ Q Rg a := by
    rw [hXZ,←critical_seed_centralizer_intersection h e pr]
    exact le_inf hWZ (commutator_eq_bot_iff_le_centralizer.mp hcom)
  have hWU : ⁅X Rg z,Q Rg c⁆ ≤ U Rg z := by
    rw [←point_omega_stabilizer_commutator h e hz hk u hR z p.end_color]
    exact commutator_mono le_rfl (hQcQt.trans hQtG)
  have hsecond := commutator_mono hWK (le_rfl : Q Rg c ≤ Q Rg c)
  refine ⟨le_inf hWU (hWK.trans inf_le_right),hsecond,?_⟩
  apply le_bot_iff.mp
  exact (commutator_mono hsecond le_rfl).trans_eq
    (commutator_eq_bot_iff_le_centralizer.mpr
      ((point_critical_seed_kernel_line_le_midpoint_omega h e hz hk u hR p).trans
        (le_centralizer_iff.mp (Q_le_centralizer_X Rg c))))


include h e hz hk in
private theorem cover_actor_le_of_central_displacement
    (A D : Subgroup M) (hA : IsPGroup 2 A)
    (hne : ¬ A ≤ pCore 2 M)
    (hindex : (centralizer (A : Set M)).relIndex W ≤ 2)
    (hcomm : ⁅W,D⁆ ≤ ⁅W,A⁆ ⊔ (W ⊓ center M)) :
    D ≤ extensionKernel h ⊔ A := by
  let := h.relative_normal
  let f := coverMap h e hz hk
  let Dnat := subspaceCommutator (naturalRepresentation (Fin 6)) ⊤ (A.map π)
  let T := (Dnat.comap f).toAddSubgroup.toSubgroup'.map (W).subtype
  have hnA : A.map π ≠ ⊥ := by
    intro he
    exact hne (two_subgroup_le_core_of_le_extensionKernel h hz A hA
      ((CubicAction.projection_kernel h e hz hk) ▸ (map_eq_bot_iff A).mp he))
  have hsmall : fixedCodim (coverAction h e hz hk) (A.map π) ≤ 1 := by
    rw [NormalElementaryQuotient.centralizer_index_eq_fixedCodim
      W π (CubicEven.projection_surjective h e hz hk)
      (CubicAction.moved_projection_kernel h e hz hk)] at hindex
    exact (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp hindex
  have hnat : fixedCodim (naturalRepresentation (Fin 6)) (A.map π) ≤ 1 :=
    (fixedCodim_le_of_equivariant_surjection (coverAction h e hz hk)
      (naturalRepresentation (Fin 6)) f (coverMap_surjective h e hz hk)
      (coverMap_equivariant h e hz hk) (A.map π)).trans hsmall
  have hT : ⁅W,A⁆ ⊔ (W ⊓ center M) ≤ T := by
    apply sup_le
    · apply commutator_le.mpr
      intro v hv a ha
      have hc : ⁅v,a⁆ ∈ W := (commutator_le_left W A)
        (commutator_mem_commutator hv ha)
      refine ⟨⟨⁅v,a⁆,hc⟩,?_,rfl⟩
      change f (Additive.ofMul (⟨⁅v,a⁆,hc⟩ : W)) ∈ Dnat
      rw [NormalElementaryQuotient.vector_commutator W π
        (CubicEven.projection_surjective h e hz hk)
        (CubicAction.moved_projection_kernel h e hz hk) ⟨v,hv⟩ a,map_sub]
      change f (Additive.ofMul ⟨v,hv⟩) -
        f (coverAction h e hz hk (π a) (Additive.ofMul ⟨v,hv⟩)) ∈ Dnat
      rw [coverMap_equivariant]
      apply Dnat.neg_mem_iff.mp
      rw [neg_sub]
      exact Submodule.subset_span ⟨π a,mem_map_of_mem π ha,_,Submodule.mem_top,rfl⟩
    · rintro v ⟨hv,hvc⟩
      refine ⟨⟨v,hv⟩,?_,rfl⟩
      change f (Additive.ofMul (⟨v,hv⟩ : W)) ∈ Dnat
      have he : f (Additive.ofMul (⟨v,hv⟩ : W)) = 0 :=
        ((Classical.choose_spec (CubicAction.moved_natural_projection h e hz hk)).2.1 _).mpr
          (center_le_centralizer _ hvc)
      rw [he]
      exact Dnat.zero_mem
  have hspace : subspaceCommutator (coverAction h e hz hk) ⊤ (D.map π) ≤ Dnat.comap f := by
    rw [←NormalElementaryQuotient.commutatorSpace_eq W π
      (CubicEven.projection_surjective h e hz hk)
      (CubicAction.moved_projection_kernel h e hz hk) D]
    intro v hv
    change (v.toMul : M) ∈ ⁅W,D⁆ at hv
    obtain ⟨w,hw,he⟩ := hT (hcomm hv)
    have he' : w = v.toMul := Subtype.ext he
    change Additive.ofMul w ∈ Dnat.comap f at hw
    simpa only [he',ofMul_toMul] using hw
  have hm : subspaceCommutator (naturalRepresentation (Fin 6)) ⊤ (D.map π) =
      (subspaceCommutator (coverAction h e hz hk) ⊤ (D.map π)).map f := by
    have hh := subspaceCommutator_map_embedding (naturalRepresentation (Fin 6))
      (coverAction h e hz hk) (MonoidHom.id _) f
      (fun g v => (coverMap_equivariant h e hz hk g v).symm) (D.map π) ⊤
    have hf : f.range = ⊤ := LinearMap.range_eq_top.mpr (coverMap_surjective h e hz hk)
    simpa only [Submodule.map_top,hf,map_id] using hh
  have him : D.map π ≤ A.map π := small_actor_le_of_moved_le _ _ hnA hnat
    (hm ▸ Submodule.map_le_iff_le_comap.mpr hspace)
  have hle := (le_comap_map π D).trans (comap_mono him)
  rw [Subgroup.comap_map_eq,CubicAction.projection_kernel h e hz hk] at hle
  exact hle.trans_eq (sup_comm _ _)

include h e hz hk in
/-- The entire midpoint-core movement exceeds the critical attachment plane.
The proof compares the actual natural quotient, retaining its central kernel. -/
theorem point_full_omega_midpoint_movement_not_le_plane
    (u : S) (hR : (Rg).map π ≤ pointCore.map (MulAut.conj u).toMonoidHom)
    {a z : Vertex Rg} (p : CriticalPath Rg (sourceGeometry h) a z) :
    ¬ ⁅X Rg z,Q Rg (p.walk.getVert 2)⁆ ≤
      ⁅Z Rg a,Z Rg z⁆ ⊔
        (U Rg z ⊓ centralizer (stabilizer Rg z : Set (FreeAmalgam Rg))) := by
  let c := p.walk.getVert 2
  have hl : p.walk.length = 4 := p.length_eq_b.trans (point_image_distance_eq_four h e hz hk u hR)
  have hc : color Rg c = false := (p.vertex_color (by omega)).mpr (by decide)
  have hAG := critical_Z_le_stabilizer Rg (sourceGeometry h) z p.end_color
    (by rw [(sourceGeometry h).distance_constant _ p.end_color]; exact sourceDistance_pos h)
    (critical_reverse Rg (sourceGeometry h) (sourceEdgeCentralizer h e) a p.start_color
      (by rw [(sourceGeometry h).distance_constant _ p.start_color]; exact sourceDistance_pos h)
      z p.end_color p.critical)
  have hBG : Q Rg c ≤ stabilizer Rg z := Q_le_stabilizer_of_dist_le_two c z hc p.end_color
    (by rw [p.dist_end,hl])
  obtain ⟨i,hi,hir,hiQ,hiE,hiU,_⟩ := graph_cover h e hz hk z p.end_color
  let A := (Z Rg a).comap i
  let B := (Q Rg c).comap i
  have hmA : A.map i = Z Rg a := map_comap_eq_self (hAG.trans_eq hir.symm)
  have hmB : B.map i = Q Rg c := map_comap_eq_self (hBG.trans_eq hir.symm)
  let := (sourceGeometry h).Z_elementary (sourceDistance_pos h) a p.start_color
  have hAp : IsPGroup 2 A := (IsElementaryAbelian.isPGroup 2 (Z Rg a)).comap_of_injective i hi
  have hBp : IsPGroup 2 B := (Q_isPGroup Rg h.relative_radical.isPGroup h.relative_radical.twoCore_le c hc).comap_of_injective i hi
  have hAn : ¬ A ≤ pCore 2 M := by
    intro hle
    exact p.critical.2 (by
      have hh := map_mono (f := i) hle
      rwa [hmA,hiQ] at hh)
  have hidx : (centralizer (A : Set M)).relIndex W ≤ 2 := by
    rw [←inf_relIndex_right,inf_comm,←relIndex_map_map_of_injective _ _ hi,
      ←map_inf_centralizer_of_injective i hi,hiU,hmA,inf_relIndex_left]
    have hQC : Q Rg a ≤ centralizer (Z Rg a : Set (FreeAmalgam Rg)) :=
      le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp
        (Z_centralizes_Q Rg a p.start_color))
    let := finite_Z Rg z
    let : Finite (U Rg z) := Finite.of_injective (inclusion (DistanceEight.U_le_Z Rg z)) (inclusion_injective _)
    exact ((relIndex_le_of_le_left hQC index_ne_zero_of_finite).trans
      (relIndex_le_of_le_right (DistanceEight.U_le_Z Rg z) index_ne_zero_of_finite)).trans_eq
        (point_image_critical_indices_two h e hz hk u hR p).2.1
  let pr := CriticalPath.ofPair (geometry := sourceGeometry h) p.end_color
    (critical_reverse Rg (sourceGeometry h) (sourceEdgeCentralizer h e) a p.start_color
      (by rw [(sourceGeometry h).distance_constant _ p.start_color]; exact sourceDistance_pos h)
      z p.end_color p.critical)
  have hline : ⁅U Rg z,Z Rg a⁆ = ⁅Z Rg a,Z Rg z⁆ := by
    rw [small_critical_moving_commutator_eq h e hz hk pr (by
      rw [(point_image_critical_indices_two h e hz hk u hR p).2.1]; decide),commutator_comm]
  have hcent : (W ⊓ center M).map i =
      U Rg z ⊓ centralizer (stabilizer Rg z : Set (FreeAmalgam Rg)) := by
    rw [show center M = centralizer ((⊤ : Subgroup M) : Set M) by
      rw [coe_top,centralizer_univ],←map_inf_centralizer_of_injective i hi,
      hiU,←MonoidHom.range_eq_map,hir]
  intro hbound
  have hcomm : ⁅W,B⁆ ≤ ⁅W,A⁆ ⊔ (W ⊓ center M) := by
    apply (map_le_map_iff_of_injective hi).mp
    rw [Subgroup.map_sup,map_commutator (W),map_commutator (W),hiU,hmA,hmB,hline,hcent]
    exact (commutator_mono (DistanceEight.U_le_Z Rg z |>.trans
      ((point_omega_eq_seed h e hz hk u hR z p.end_color).symm.le)) le_rfl).trans hbound
  have hle := cover_actor_le_of_central_displacement h e hz hk A B hAp hAn hidx hcomm
  have him : B.map π ≤ A.map π := by
    have hh := map_mono (f := π) hle
    rwa [Subgroup.map_sup,←CubicAction.projection_kernel h e hz hk,
      (Subgroup.map_eq_bot_iff (π).ker).mpr le_rfl,bot_sup_eq] at hh
  have hcard := card_le_of_le him
  rw [CubicAction.permutation_image_card_of_two h e hz hk B hBp,
    CubicAction.permutation_image_card_of_two h e hz hk A hAp] at hcard
  have hidxB : (pCore 2 M).relIndex B = (Q Rg z).relIndex (Q Rg c) := by
    rw [←relIndex_map_map_of_injective _ _ hi,hiQ,hmB]
  have hidxA : (pCore 2 M).relIndex A = 2 := by
    rw [←relIndex_map_map_of_injective _ _ hi,hiQ,hmA]
    exact (point_image_critical_indices_two h e hz hk u hR p).1
  rw [hidxB,hidxA] at hcard
  rcases (point_critical_midpoint_core_bounds h e hz hk u hR p).2.1 with h4|h8
  · change (Q Rg z).relIndex (Q Rg c) = 4 at h4
    omega
  · change (Q Rg z).relIndex (Q Rg c) = 8 at h8
    omega

include h e hz hk in
/-- The full omega displacement under the midpoint core has order eight or
sixteen. The critical attachment plane is a proper subgroup of it. -/
theorem point_full_omega_midpoint_core_growth
    (u : S) (hR : (Rg).map π ≤ pointCore.map (MulAut.conj u).toMonoidHom)
    {a z : Vertex Rg} (p : CriticalPath Rg (sourceGeometry h) a z) :
    let c := p.walk.getVert 2
    let H := ⁅Z Rg z ⊓ Q Rg a,Q Rg c⁆
    let D := ⁅Z Rg a,Z Rg z⁆
    let F := ⁅X Rg z,Q Rg c⁆
    H ⊔ D < F ∧ (Nat.card F = 8 ∨ Nat.card F = 16) := by
  let c := p.walk.getVert 2
  let H := ⁅Z Rg z ⊓ Q Rg a,Q Rg c⁆
  let D := ⁅Z Rg a,Z Rg z⁆
  let F := ⁅X Rg z,Q Rg c⁆
  have hl : p.walk.length = 4 := p.length_eq_b.trans (point_image_distance_eq_four h e hz hk u hR)
  have hFX := (point_full_omega_midpoint_core_movement h e hz hk u hR p).1
  have hFU : F ≤ U Rg z := hFX.trans inf_le_left
  have hXZ : X Rg z = Z Rg z := point_omega_eq_seed h e hz hk u hR z p.end_color
  have hHF : H ≤ F := commutator_mono (inf_le_left.trans hXZ.symm.le) le_rfl
  let pr := CriticalPath.ofPair (geometry := sourceGeometry h) p.end_color
    (critical_reverse Rg (sourceGeometry h) (sourceEdgeCentralizer h e) a p.start_color
      (by rw [(sourceGeometry h).distance_constant _ p.start_color]; exact sourceDistance_pos h)
      z p.end_color p.critical)
  have hDm : D = ⁅U Rg z,Z Rg a⁆ := by
    rw [small_critical_moving_commutator_eq h e hz hk pr (by
      rw [(point_image_critical_indices_two h e hz hk u hR p).2.1]; decide),commutator_comm]
  have hZaQc : Z Rg a ≤ Q Rg c := by
    apply Z_le_Q_of_dist_lt Rg a ((sourceGeometry h).exists_critical a p.start_color)
    rw [(sourceGeometry h).distance_constant _ p.start_color,p.dist_start (by omega)]
    change 2 < sourceDistance h
    rw [point_image_distance_eq_four h e hz hk u hR]
    decide
  have hDF : D ≤ F := by
    rw [hDm]
    exact commutator_mono ((DistanceEight.U_le_Z Rg z).trans hXZ.symm.le) hZaQc
  have hplane := point_critical_midpoint_attachment_plane h e hz hk u hR p
  have hproper : H ⊔ D < F := lt_of_le_not_ge (sup_le hHF hDF) (by
    intro he
    apply point_full_omega_midpoint_movement_not_le_plane h e hz hk u hR p
    exact he.trans hplane.2.1.le)
  have hUcard := point_graph_moved_card_eq_thirtytwo h e hz hk u hR z p.end_color
  let := finite_Z Rg z
  let : Finite (U Rg z) := Finite.of_injective (inclusion (DistanceEight.U_le_Z Rg z)) (inclusion_injective _)
  let : Finite F := Finite.of_injective (inclusion hFU) (inclusion_injective _)
  let : Finite (H ⊔ D : Subgroup (FreeAmalgam Rg)) :=
    Finite.of_injective (inclusion hproper.le) (inclusion_injective _)
  let := (sourceGeometry h).Z_elementary (sourceDistance_pos h) z p.end_color
  have hHZ : H ≤ Z Rg z := (hHF.trans hFU).trans (DistanceEight.U_le_Z Rg z)
  have hDZ : D ≤ Z Rg z := (hDF.trans hFU).trans (DistanceEight.U_le_Z Rg z)
  have hN : D ≤ normalizer (H : Set (FreeAmalgam Rg)) :=
    ((hDZ.trans (le_centralizer_iff_isMulCommutative.mpr inferInstance)).trans
      (centralizer_le hHZ)).trans (Subgroup.centralizer_le_normalizer _)
  have hHcard : Nat.card H = 2 := (point_critical_radius_cross_kernel_line_at h e hz hk u hR p).1
  have hDcard : Nat.card D = 2 := (point_image_critical_indices_two h e hz hk u hR p).2.2
  have hPcard : Nat.card (H ⊔ D : Subgroup (FreeAmalgam Rg)) = 4 := by
    rw [card_sup_eq_mul_of_normalizes_of_disjoint H D hN (disjoint_iff.mpr hplane.1),hHcard,hDcard]
  have hlo : 4 < Nat.card F := by
    by_contra! hno
    have he : H ⊔ D = F := eq_of_le_of_card_ge hproper.le (by omega)
    exact hproper.ne he
  have hup : Nat.card F < 32 := by
    by_contra! hno
    have he : F = U Rg z := eq_of_le_of_card_ge hFU (by omega)
    have hzero : D = ⊥ := by
      rw [hDm]
      apply commutator_eq_bot_iff_le_centralizer.mpr
      exact (he.symm.le.trans (hFX.trans inf_le_right)).trans
        (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp
          (Z_centralizes_Q Rg a p.start_color)))
    rw [hzero,card_bot] at hDcard
    omega
  obtain ⟨k,hkcard⟩ := ((IsElementaryAbelian.isPGroup 2 (Z Rg z)).to_le
    (hFU.trans (DistanceEight.U_le_Z Rg z))).exists_card_eq
  change Nat.card F = 2^k at hkcard
  have hk5 : k ≤ 5 := (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp
    (show 2^k ≤ 2^5 by omega)
  refine ⟨hproper,?_⟩
  change Nat.card F = 8 ∨ Nat.card F = 16
  interval_cases k <;> simp only [Nat.reducePow] at hkcard <;> omega


include h e hz hk in
/-- On the original selected pair, both full midpoint-core movements have
order eight or sixteen. Their next commutators lie in the same shifted line,
which the generating edge fixes under the entire original stabilizer. -/
theorem point_generating_full_core_movement
    (u : S) (hR : (Rg).map π ≤ pointCore.map (MulAut.conj u).toMonoidHom)
    {z c d : Vertex Rg}
    (p : CriticalPath Rg (sourceGeometry h) (alpha Rg) z)
    (q : CriticalPath Rg (sourceGeometry h) d c)
    (hpc : p.walk.getVert 2 = c) (hqa : q.walk.getVert 2 = alpha Rg)
    (hgen : Q Rg (q.walk.getVert 1) ⊔ Z Rg z = stabilizer Rg (alpha Rg))
    (hne : ⁅U Rg d ⊓ Q Rg c,X Rg z ⊓ Q Rg (alpha Rg)⁆ ≠ ⊥) :
    let H := ⁅U Rg d ⊓ Q Rg c,X Rg z ⊓ Q Rg (alpha Rg)⁆
    let Fz := ⁅X Rg z,Q Rg c⁆
    let Fd := ⁅X Rg d,Q Rg (alpha Rg)⁆
    (Nat.card Fz = 8 ∨ Nat.card Fz = 16) ∧
      (Nat.card Fd = 8 ∨ Nat.card Fd = 16) ∧
      ⁅Fz,Q Rg c⁆ ⊔ ⁅Fd,Q Rg (alpha Rg)⁆ ≤ H ∧
      ⁅Fz,Q Rg c⁆ ⊔ ⁅Fd,Q Rg (alpha Rg)⁆ ≤
        centralizer (stabilizer Rg (alpha Rg) : Set (FreeAmalgam Rg)) ∧
      H ⊔ ⁅Z Rg d,Z Rg c⁆ < Fd := by
  have hb := point_image_distance_eq_four h e hz hk u hR
  have hl : q.walk.length = 4 := q.length_eq_b.trans hb
  let qr : CriticalPath Rg (sourceGeometry h) c d :=
    ⟨q.end_color,q.walk.reverse,
      by rw [SimpleGraph.Walk.length_reverse,q.shortest,SimpleGraph.dist_comm],
      critical_reverse Rg (sourceGeometry h) (sourceEdgeCentralizer h e) d q.start_color
        (by rw [(sourceGeometry h).distance_constant _ q.start_color]; exact sourceDistance_pos h)
        c q.end_color q.critical⟩
  have hqr : qr.walk.getVert 2 = alpha Rg := by
    change q.walk.reverse.getVert 2 = alpha Rg
    rw [SimpleGraph.Walk.getVert_reverse,hl]
    exact hqa
  obtain ⟨_,_,halt,_,_,_,_,_,hforward⟩ :=
    point_shifted_omega_kernel_line h e hz hk u hR p q hpc hqa
  have hback := halt.resolve_left hne
  have hfwd := hback.trans (hforward hne)
  have hp := point_full_omega_midpoint_core_movement h e hz hk u hR p
  have hd := point_full_omega_midpoint_core_movement h e hz hk u hR qr
  have hpg := point_full_omega_midpoint_core_growth h e hz hk u hR p
  have hdg := point_full_omega_midpoint_core_growth h e hz hk u hR qr
  dsimp only at hp hd hpg hdg ⊢
  rw [hpc,←hfwd] at hp hpg
  rw [hqr,←hback] at hd hdg
  rw [commutator_comm (Z Rg c)] at hdg
  have hbound := sup_le hp.2.1 hd.2.1
  exact ⟨hpg.2,hdg.2,hbound,hbound.trans
    (point_generating_shifted_kernel_central h e hz hk u hR p q hpc hqa hgen).2.1,hdg.1⟩


omit hk in
include h e hz in
/-- Whole-core application with full omega movement at both selected endpoints,
and their common second-commutator bound. -/
theorem coreExhaustion_or_cubic_full_core_movement :
    CoreExhaustion L R ∨ ∃ hk : layerKernel L R = extensionKernel h,
      Function.Surjective (CubicAction.projection h e hz hk) ∧
      2 < sourceDistance h ∧
      (∀ a : Vertex Rg, color Rg a = false →
        Nat.card (U Rg a) = 16 ∨ Nat.card (U Rg a) = 32) ∧
      ∃ u : S,
        ((Rg).map (CubicAction.projection h e hz hk) =
            pointCore.map (MulAut.conj u).toMonoidHom ∧
          sourceDistance h = 4 ∧
          (let := h.relative_normal
           ∃ E : Additive W ≃ₗ[ZMod 2] core (Fin 6),
             ∀ (g : M) (v : Additive W),
               E (Additive.ofMul (MulAut.conjNormal g v.toMul)) =
                 coreRepresentation (Fin 6) (CubicAction.projection h e hz hk g) (E v)) ∧
          (∀ a : Vertex Rg, color Rg a = false →
            Nat.card (U Rg a) = 32 ∧
            Nat.card (U Rg a ⊓ centralizer (stabilizer Rg a : Set (FreeAmalgam Rg)) :
              Subgroup (FreeAmalgam Rg)) = 2) ∧
          (∀ a : Vertex Rg, color Rg a = false →
            X Rg a = U Rg a ⊔
              (X Rg a ⊓ centralizer (stabilizer Rg a : Set (FreeAmalgam Rg))) ∧
            X Rg a = Z Rg a) ∧
          (∀ a z : Vertex Rg, ∀ p : CriticalPath Rg (sourceGeometry h) a z,
            let c := p.walk.getVert 2
            let H := ⁅Z Rg z ⊓ Q Rg a,Q Rg c⁆
            let D := ⁅Z Rg a,Z Rg z⁆
            let C := U Rg z ⊓ centralizer (stabilizer Rg z : Set (FreeAmalgam Rg))
            H ⊓ D = ⊥ ∧ H ⊔ D = D ⊔ C ∧ C ≤ ⁅U Rg z,Q Rg c⁆) ∧
          (∃ z, ∃ p : CriticalPath Rg (sourceGeometry h) (alpha Rg) z,
            2 < (B Rg (alpha Rg) ((sourceGeometry h).Z_normal _)).relIndex
              (U Rg (p.walk.getVert 2)) ∧
            ∃ d, ∃ q : CriticalPath Rg (sourceGeometry h) d
                (p.walk.getVert (p.walk.length-2)),
              ∃ x : FreeAmalgam Rg, x ∈ stabilizer Rg (alpha Rg) ∧
              act Rg x (p.walk.getVert 2) = d ∧
              q.walk.getVert 2 = alpha Rg ∧
              Q Rg (q.walk.getVert 1) ⊔ Z Rg z = stabilizer Rg (alpha Rg) ∧
              let c := p.walk.getVert (p.walk.length-2)
              let H := ⁅U Rg d ⊓ Q Rg c,X Rg z ⊓ Q Rg (alpha Rg)⁆
              let C := U Rg z ⊓ centralizer (stabilizer Rg z : Set (FreeAmalgam Rg))
              H = ⁅Z Rg d ⊓ Q Rg c,Q Rg (alpha Rg)⁆ ∧
              H = ⁅Z Rg z ⊓ Q Rg (alpha Rg),Q Rg c⁆ ∧
              Nat.card H = 2 ∧
              H ≤ centralizer (stabilizer Rg (alpha Rg) : Set (FreeAmalgam Rg)) ∧
              ¬ H ≤ centralizer (stabilizer Rg z : Set (FreeAmalgam Rg)) ∧
              C ≤ Z Rg (alpha Rg) ∧
              ¬ C ≤ centralizer (stabilizer Rg (alpha Rg) : Set (FreeAmalgam Rg)) ∧
              ⁅C,Q Rg (q.walk.getVert 1)⁆ ≠ ⊥ ∧
              ¬ H ≤ centralizer (stabilizer Rg d : Set (FreeAmalgam Rg)) ∧
              ((Q Rg z).relIndex (Q Rg c) = 4 ∨ (Q Rg z).relIndex (Q Rg c) = 8) ∧
              ((Q Rg d).relIndex (Q Rg (alpha Rg)) = 4 ∨
                (Q Rg d).relIndex (Q Rg (alpha Rg)) = 8) ∧
              (Q Rg z).relIndex (V Rg c) = 2 ∧
              (Q Rg d).relIndex (V Rg (alpha Rg)) = 2 ∧
              ¬ Q Rg c ≤ Q Rg z ⊔ V Rg c ∧
              ¬ Q Rg (alpha Rg) ≤ Q Rg d ⊔ V Rg (alpha Rg) ∧
              let D₀ := ⁅Z Rg d,Z Rg c⁆
              let C₀ := U Rg c ⊓ centralizer (stabilizer Rg c : Set (FreeAmalgam Rg))
              (U Rg d ⊓ centralizer (stabilizer Rg d : Set (FreeAmalgam Rg))) = C₀ ∧
              H ⊔ D₀ = D₀ ⊔ C₀ ∧
              Nat.card (H ⊔ D₀ : Subgroup (FreeAmalgam Rg)) = 4 ∧
              H ⊔ D₀ ≤ U Rg d ⊓ U Rg c ⊓
                centralizer (stabilizer Rg (alpha Rg) : Set (FreeAmalgam Rg)) ∧
              let Fz := ⁅X Rg z,Q Rg c⁆
              let Fd := ⁅X Rg d,Q Rg (alpha Rg)⁆
              (Nat.card Fz = 8 ∨ Nat.card Fz = 16) ∧
              (Nat.card Fd = 8 ∨ Nat.card Fd = 16) ∧
              ⁅Fz,Q Rg c⁆ ⊔ ⁅Fd,Q Rg (alpha Rg)⁆ ≤ H ∧
              ⁅Fz,Q Rg c⁆ ⊔ ⁅Fd,Q Rg (alpha Rg)⁆ ≤
                centralizer (stabilizer Rg (alpha Rg) : Set (FreeAmalgam Rg)) ∧
              H ⊔ D₀ < Fd)) ∨
        (Rg).map (CubicAction.projection h e hz hk) =
          D.map (MulAut.conj u).toMonoidHom ∨
        (Rg).map (CubicAction.projection h e hz hk) =
          borel.map (MulAut.conj u).toMonoidHom := by
  rcases coreExhaustion_or_cubic_common_attachment h e hz with
    hex | ⟨hk,hs,hb,hcovers,u,hpoint | hplane | hsylow⟩
  · exact Or.inl hex
  · rcases hpoint with ⟨hpoint,hb4,hmodel,hsize,hX,hplanes,z,p,hstrict,
      d,q,x,hx,hxc,hqa,hgen,hback,hfull,hcard,hcentral,hnon,hCZ,hCn,hmove,
      hdnon,hpb,hqb,hpV,hqV,hpn,hqn,hattach,hplane,hplaneCard,hplaneLe⟩
    have hl : p.walk.length = 4 := p.length_eq_b.trans hb4
    have hpc : p.walk.getVert 2 = p.walk.getVert (p.walk.length-2) := by rw [hl]
    have hne : ⁅U Rg d ⊓ Q Rg (p.walk.getVert (p.walk.length-2)),
        X Rg z ⊓ Q Rg (alpha Rg)⁆ ≠ ⊥ := by
      intro he
      rw [he,card_bot] at hcard
      omega
    have hcores := point_generating_full_core_movement h e hz hk u hpoint.le
      p q hpc hqa hgen hne
    exact Or.inr ⟨hk,hs,hb,hcovers,u,Or.inl ⟨hpoint,hb4,hmodel,hsize,hX,hplanes,
      z,p,hstrict,d,q,x,hx,hxc,hqa,hgen,hback,hfull,hcard,hcentral,hnon,hCZ,hCn,hmove,
      hdnon,hpb,hqb,hpV,hqV,hpn,hqn,hattach,hplane,hplaneCard,hplaneLe,hcores⟩⟩
  · exact Or.inr ⟨hk,hs,hb,hcovers,u,Or.inr (Or.inl hplane)⟩
  · exact Or.inr ⟨hk,hs,hb,hcovers,u,Or.inr (Or.inr hsylow)⟩

omit hk in
include h e hz in
/-- Literal C.1.32 application retaining the entire moving covers and the
full midpoint-core movement on the same selected configuration. -/
theorem rankTwo_or_cubic_full_core_movement :
    RankTwoAlternatives L R ∨ ∃ hk : layerKernel L R = extensionKernel h,
      Function.Surjective (CubicAction.projection h e hz hk) ∧
      2 < sourceDistance h ∧
      (∀ a : Vertex Rg, color Rg a = false →
        Nat.card (U Rg a) = 16 ∨ Nat.card (U Rg a) = 32) ∧
      ∃ u : S,
        ((Rg).map (CubicAction.projection h e hz hk) =
            pointCore.map (MulAut.conj u).toMonoidHom ∧
          sourceDistance h = 4 ∧
          (let := h.relative_normal
           ∃ E : Additive W ≃ₗ[ZMod 2] core (Fin 6),
             ∀ (g : M) (v : Additive W),
               E (Additive.ofMul (MulAut.conjNormal g v.toMul)) =
                 coreRepresentation (Fin 6) (CubicAction.projection h e hz hk g) (E v)) ∧
          (∀ a : Vertex Rg, color Rg a = false →
            Nat.card (U Rg a) = 32 ∧
            Nat.card (U Rg a ⊓ centralizer (stabilizer Rg a : Set (FreeAmalgam Rg)) :
              Subgroup (FreeAmalgam Rg)) = 2) ∧
          (∀ a : Vertex Rg, color Rg a = false →
            X Rg a = U Rg a ⊔
              (X Rg a ⊓ centralizer (stabilizer Rg a : Set (FreeAmalgam Rg))) ∧
            X Rg a = Z Rg a) ∧
          (∀ a z : Vertex Rg, ∀ p : CriticalPath Rg (sourceGeometry h) a z,
            let c := p.walk.getVert 2
            let H := ⁅Z Rg z ⊓ Q Rg a,Q Rg c⁆
            let D := ⁅Z Rg a,Z Rg z⁆
            let C := U Rg z ⊓ centralizer (stabilizer Rg z : Set (FreeAmalgam Rg))
            H ⊓ D = ⊥ ∧ H ⊔ D = D ⊔ C ∧ C ≤ ⁅U Rg z,Q Rg c⁆) ∧
          (∃ z, ∃ p : CriticalPath Rg (sourceGeometry h) (alpha Rg) z,
            2 < (B Rg (alpha Rg) ((sourceGeometry h).Z_normal _)).relIndex
              (U Rg (p.walk.getVert 2)) ∧
            ∃ d, ∃ q : CriticalPath Rg (sourceGeometry h) d
                (p.walk.getVert (p.walk.length-2)),
              ∃ x : FreeAmalgam Rg, x ∈ stabilizer Rg (alpha Rg) ∧
              act Rg x (p.walk.getVert 2) = d ∧
              q.walk.getVert 2 = alpha Rg ∧
              Q Rg (q.walk.getVert 1) ⊔ Z Rg z = stabilizer Rg (alpha Rg) ∧
              let c := p.walk.getVert (p.walk.length-2)
              let H := ⁅U Rg d ⊓ Q Rg c,X Rg z ⊓ Q Rg (alpha Rg)⁆
              let C := U Rg z ⊓ centralizer (stabilizer Rg z : Set (FreeAmalgam Rg))
              H = ⁅Z Rg d ⊓ Q Rg c,Q Rg (alpha Rg)⁆ ∧
              H = ⁅Z Rg z ⊓ Q Rg (alpha Rg),Q Rg c⁆ ∧
              Nat.card H = 2 ∧
              H ≤ centralizer (stabilizer Rg (alpha Rg) : Set (FreeAmalgam Rg)) ∧
              ¬ H ≤ centralizer (stabilizer Rg z : Set (FreeAmalgam Rg)) ∧
              C ≤ Z Rg (alpha Rg) ∧
              ¬ C ≤ centralizer (stabilizer Rg (alpha Rg) : Set (FreeAmalgam Rg)) ∧
              ⁅C,Q Rg (q.walk.getVert 1)⁆ ≠ ⊥ ∧
              ¬ H ≤ centralizer (stabilizer Rg d : Set (FreeAmalgam Rg)) ∧
              ((Q Rg z).relIndex (Q Rg c) = 4 ∨ (Q Rg z).relIndex (Q Rg c) = 8) ∧
              ((Q Rg d).relIndex (Q Rg (alpha Rg)) = 4 ∨
                (Q Rg d).relIndex (Q Rg (alpha Rg)) = 8) ∧
              (Q Rg z).relIndex (V Rg c) = 2 ∧
              (Q Rg d).relIndex (V Rg (alpha Rg)) = 2 ∧
              ¬ Q Rg c ≤ Q Rg z ⊔ V Rg c ∧
              ¬ Q Rg (alpha Rg) ≤ Q Rg d ⊔ V Rg (alpha Rg) ∧
              let D₀ := ⁅Z Rg d,Z Rg c⁆
              let C₀ := U Rg c ⊓ centralizer (stabilizer Rg c : Set (FreeAmalgam Rg))
              (U Rg d ⊓ centralizer (stabilizer Rg d : Set (FreeAmalgam Rg))) = C₀ ∧
              H ⊔ D₀ = D₀ ⊔ C₀ ∧
              Nat.card (H ⊔ D₀ : Subgroup (FreeAmalgam Rg)) = 4 ∧
              H ⊔ D₀ ≤ U Rg d ⊓ U Rg c ⊓
                centralizer (stabilizer Rg (alpha Rg) : Set (FreeAmalgam Rg)) ∧
              let Fz := ⁅X Rg z,Q Rg c⁆
              let Fd := ⁅X Rg d,Q Rg (alpha Rg)⁆
              (Nat.card Fz = 8 ∨ Nat.card Fz = 16) ∧
              (Nat.card Fd = 8 ∨ Nat.card Fd = 16) ∧
              ⁅Fz,Q Rg c⁆ ⊔ ⁅Fd,Q Rg (alpha Rg)⁆ ≤ H ∧
              ⁅Fz,Q Rg c⁆ ⊔ ⁅Fd,Q Rg (alpha Rg)⁆ ≤
                centralizer (stabilizer Rg (alpha Rg) : Set (FreeAmalgam Rg)) ∧
              H ⊔ D₀ < Fd)) ∨
        (Rg).map (CubicAction.projection h e hz hk) =
          D.map (MulAut.conj u).toMonoidHom ∨
        (Rg).map (CubicAction.projection h e hz hk) =
          borel.map (MulAut.conj u).toMonoidHom :=
  (coreExhaustion_or_cubic_full_core_movement h e hz).imp (rankTwo_of_exhaustion h e hz) id

end AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicFull
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
