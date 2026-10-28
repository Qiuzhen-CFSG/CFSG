module

public import CFSG.Quasithin.Chapter14.Section04.LargerDimension.Orthogonal.Lift.Centralizers
public import Theory.GroupTheory.PCoreImage
public import Theory.GroupTheory.SylowKernelCore

/-!
# Core calculations for the orthogonal lift

The three-subgroups lemma shows that C_U(i) centralizes [U,i]. The
extraspecial abelian bound therefore identifies C_U(i) with the order-32
base. Factoring UD then gives C_{UD}(i)=D. A two-core bound in the actual
quotient H/O₂(H) pulls back to UD, so intersecting with C_H(i) proves
D=O₂(C_H(i)). The same quotient argument identifies O₂(K₀UD)=UD.

The two quotient-core bounds are explicit model premises. This module
proves their lift through the literal subgroup subtype maps; it does not
assert that the case-(3) model calculations have been completed.

Source: Aschbacher–Smith, Lemma 14.4.9, printed p.1010.
-/

public section
open Subgroup
open scoped commutatorElement IsMulCommutative Pointwise
namespace CFSG.Quasithin.Chapter14.Section04.LargerDimension.Orthogonal
variable {G : Type*} [Group G] [Finite G]

theorem liftBase_eq_involution_centralizer
    (U : Subgroup G) [IsExtraspecial 2 U] (z i : G)
    (hZ : (center U).map U.subtype = zpowers z)
    (hiU : i ∈ normalizer (U : Set G))
    (hiz : i ∈ centralizer ({z} : Set G))
    (hUcard : Nat.card U = 512)
    (hD : IsElementaryAbelian 2 (centralizerLift U z i))
    (hA : IsElementaryAbelian 2 (liftBase U z i))
    (hAcard : Nat.card (liftBase U z i) = 32) :
    U ⊓ centralizer ({i} : Set G) = liftBase U z i := by
  let A := liftBase U z i
  let C := U ⊓ centralizer ({i} : Set G)
  have hCUi : ⁅C, zpowers i⁆ = ⊥ := by
    apply commutator_eq_bot_iff_le_centralizer.mpr
    simpa only [zpowers_eq_closure, centralizer_closure] using
      (inf_le_right : C ≤ centralizer ({i} : Set G))
  have hUU : ⁅U,U⁆ ≤ zpowers z := by
    have hh := map_mono (f := U.subtype)
      (IsExtraspecial.quotient_elementary_abelian 2 U).commutator_le_center_of_central_quotient
    simpa only [map_subtype_commutator, hZ] using hh
  have hZi : zpowers z ≤ centralizer (zpowers i : Set G) := by
    rw [zpowers_eq_closure i, centralizer_closure]
    exact zpowers_le.mpr (mem_centralizer_singleton_iff.mpr
      (mem_centralizer_singleton_iff.mp hiz).symm)
  have htriple : ⁅⁅U,zpowers i⁆,C⁆ = ⊥ := by
    apply commutator_commutator_eq_bot_of_rotate
    · rw [commutator_comm (zpowers i) C, hCUi, commutator_bot_left]
    · apply commutator_eq_bot_iff_le_centralizer.mpr
      exact ((commutator_mono inf_le_left le_rfl).trans hUU).trans hZi
  have hCA : C ≤ centralizer (A : Set G) := by
    apply le_centralizer_iff.mpr
    apply sup_le
    · exact commutator_eq_bot_iff_le_centralizer.mp htriple
    · rw [← hZ]
      rintro _ ⟨a, ha, rfl⟩ u hu
      exact congrArg Subtype.val (mem_center_iff.mp ha (⟨u, hu.1⟩ : U))
  have hself := liftBase_self_centralizer U z i hZ hiU hUcard hA hAcard
  apply le_antisymm
  · exact (le_inf inf_le_left hCA).trans (le_of_eq hself)
  · have hzU : zpowers z ≤ U := by rw [← hZ]; exact map_subtype_le _
    have hAU : A ≤ U := sup_le
      (le_normalizer_iff_commutator_le_left.mp (zpowers_le.mpr hiU)) hzU
    have hAD : A ≤ centralizerLift U z i := sup_le
      (le_sup_left.trans le_sup_left) le_sup_right
    let : IsElementaryAbelian 2 (centralizerLift U z i) := hD
    apply le_inf hAU
    intro a ha
    exact mem_centralizer_singleton_iff.mpr
      (congrArg Subtype.val (mul_comm (⟨a,hAD ha⟩ : centralizerLift U z i)
        ⟨i,(show zpowers i ≤ centralizerLift U z i from le_sup_right.trans le_sup_left)
          (mem_zpowers i)⟩))


private theorem core_le_join_of_quotient_core_le
    (H C : Subgroup G) (i : H) (hCH : C ≤ H)
    (hbar : ((C.subgroupOf H).map (QuotientGroup.mk' (pCore 2 H))).pCoreIn 2 ≤
      (zpowers i).map (QuotientGroup.mk' (pCore 2 H))) :
    C.pCoreIn 2 ≤ H.pCoreIn 2 ⊔ zpowers (i : G) := by
  let q := QuotientGroup.mk' (pCore 2 H)
  have hk : IsPGroup 2 q.ker := by
    rw [QuotientGroup.ker_mk']
    exact pCore_isPGroup
  have hh : (C.subgroupOf H).pCoreIn 2 ≤ zpowers i ⊔ pCore 2 H := by
    have hm := map_pCoreIn_of_ker_isPGroup q hk (C.subgroupOf H)
    have hle := hm.le.trans hbar
    simpa only [q, QuotientGroup.ker_mk'] using map_le_map_iff.mp hle
  have hm := map_mono (f := H.subtype) hh
  rw [map_pCoreIn_of_injective 2 _ _ H.subtype_injective,
    map_subgroupOf_eq_of_le hCH, Subgroup.map_sup, MonoidHom.map_zpowers] at hm
  exact hm.trans (le_of_eq (sup_comm _ _))

omit [Finite G] in
theorem centralizerLift_centralizer_in_join
    (U : Subgroup G) (z i : G)
    (hiU : i ∈ normalizer (U : Set G))
    (hzU : zpowers z ≤ U)
    (hD : IsElementaryAbelian 2 (centralizerLift U z i))
    (hCU : U ⊓ centralizer ({i} : Set G) = liftBase U z i) :
    (U ⊔ centralizerLift U z i) ⊓ centralizer ({i} : Set G) =
      centralizerLift U z i := by
  let D := centralizerLift U z i
  let : IsElementaryAbelian 2 D := hD
  have hAD : liftBase U z i ≤ D := sup_le (le_sup_left.trans le_sup_left) le_sup_right
  have hiD : i ∈ D := (show zpowers i ≤ D from le_sup_right.trans le_sup_left) (mem_zpowers i)
  have hDi : D ≤ centralizer ({i} : Set G) := by
    intro d hd
    exact mem_centralizer_singleton_iff.mpr ((D.le_centralizer hd) i hiD).symm
  have hBU : ⁅U,zpowers i⁆ ≤ U :=
    le_normalizer_iff_commutator_le_left.mp (zpowers_le.mpr hiU)
  have hDU : D ≤ normalizer (U : Set G) := sup_le
    (sup_le (hBU.trans U.le_normalizer) (zpowers_le.mpr hiU)) (hzU.trans U.le_normalizer)
  apply le_antisymm
  · rintro a ⟨ha,hac⟩
    have hprod : a ∈ (U : Set G) * (D : Set G) := by
      rw [← coe_mul_of_right_le_normalizer_left U D hDU]
      exact ha
    obtain ⟨u,hu,d,hd,rfl⟩ := hprod
    have hui : u ∈ centralizer ({i} : Set G) := by
      have hh := (centralizer ({i} : Set G)).mul_mem hac
        ((centralizer ({i} : Set G)).inv_mem (hDi hd))
      simpa only [mul_inv_cancel_right] using hh
    have huA : u ∈ liftBase U z i := hCU ▸ (show u ∈ U ⊓ centralizer ({i} : Set G) from ⟨hu,hui⟩)
    exact D.mul_mem (hAD huA) hd
  · exact le_inf le_sup_right hDi

theorem centralizerLift_eq_joint_core_of_quotient
    (U : Subgroup G) [IsExtraspecial 2 U] (z i : G)
    (hZ : (center U).map U.subtype = zpowers z)
    (hUcore : (centralizer ({z} : Set G)).pCoreIn 2 = U)
    (hiU : i ∈ normalizer (U : Set G))
    (hiz : i ∈ centralizer ({z} : Set G))
    (hUcard : Nat.card U = 512)
    (hD : IsElementaryAbelian 2 (centralizerLift U z i))
    (hA : IsElementaryAbelian 2 (liftBase U z i))
    (hAcard : Nat.card (liftBase U z i) = 32)
    (hmoved : Nat.card (((⁅U,zpowers i⁆).subgroupOf U).map
      (QuotientGroup.mk' (center U))) = 16)
    (hbar : (((centralizer ({z} : Set G) ⊓ centralizer ({i} : Set G)).subgroupOf
      (centralizer ({z} : Set G))).map
        (QuotientGroup.mk' (pCore 2 (centralizer ({z} : Set G))))).pCoreIn 2 ≤
      (zpowers (⟨i,hiz⟩ : centralizer ({z} : Set G))).map
        (QuotientGroup.mk' (pCore 2 (centralizer ({z} : Set G))))) :
    (centralizer ({z} : Set G) ⊓ centralizer ({i} : Set G)).pCoreIn 2 =
      centralizerLift U z i := by
  let H := centralizer ({z} : Set G)
  let C := H ⊓ centralizer ({i} : Set G)
  let D := centralizerLift U z i
  let : IsElementaryAbelian 2 D := hD
  have hHU : H ≤ normalizer (U : Set G) := by
    rw [← hUcore]
    exact H.le_normalizer.trans (normalizer_le_normalizer_characteristic_image H (pCore 2 H))
  have hCD : C ≤ normalizer (D : Set G) :=
    le_sup_left.trans (lift_normalized_by_residual_join_core U C z i hZ hiU
      (inf_le_left.trans hHU) inf_le_right hmoved)
  have hDC : D ≤ C := by
    apply le_inf
    · intro d hd
      exact mem_centralizer_singleton_iff.mpr
        ((D.le_centralizer hd) z (mem_sup_right (mem_zpowers z))).symm
    · intro d hd
      exact mem_centralizer_singleton_iff.mpr
        ((D.le_centralizer hd) i
          ((show zpowers i ≤ D from le_sup_right.trans le_sup_left) (mem_zpowers i))).symm
  apply le_antisymm
  · have hbound := core_le_join_of_quotient_core_le H C ⟨i,hiz⟩ inf_le_left hbar
    rw [hUcore] at hbound
    have hzU : zpowers z ≤ U := by rw [← hZ]; exact map_subtype_le _
    have hc := centralizerLift_centralizer_in_join U z i hiU hzU hD
      (liftBase_eq_involution_centralizer U z i hZ hiU hiz hUcard hD hA hAcard)
    apply (le_inf (hbound.trans (sup_le_sup_left
      (show zpowers i ≤ D from le_sup_right.trans le_sup_left) U))
      ((pCoreIn_le 2 C).trans inf_le_right)).trans
    exact le_of_eq hc
  · exact le_pCoreIn_of_normalizes (IsElementaryAbelian.isPGroup 2 D) hDC hCD


theorem core_join_lift_eq_residual_join_core_of_quotient
    (U : Subgroup G) [IsExtraspecial 2 U] (z i : G)
    (hZ : (center U).map U.subtype = zpowers z)
    (hUcore : (centralizer ({z} : Set G)).pCoreIn 2 = U)
    (hiU : i ∈ normalizer (U : Set G))
    (hiz : i ∈ centralizer ({z} : Set G))
    (hD : IsElementaryAbelian 2 (centralizerLift U z i))
    (hmoved : Nat.card (((⁅U,zpowers i⁆).subgroupOf U).map
      (QuotientGroup.mk' (center U))) = 16)
    (hbar : (((diagonalResidual (centralizer ({z} : Set G)) i ⊔ U ⊔
      centralizerLift U z i).subgroupOf (centralizer ({z} : Set G))).map
        (QuotientGroup.mk' (pCore 2 (centralizer ({z} : Set G))))).pCoreIn 2 ≤
      (zpowers (⟨i,hiz⟩ : centralizer ({z} : Set G))).map
        (QuotientGroup.mk' (pCore 2 (centralizer ({z} : Set G))))) :
    (diagonalResidual (centralizer ({z} : Set G)) i ⊔ U ⊔
      centralizerLift U z i).pCoreIn 2 = U ⊔ centralizerLift U z i := by
  let H := centralizer ({z} : Set G)
  let K := diagonalResidual H i
  let D := centralizerLift U z i
  let J := K ⊔ U ⊔ D
  let : IsElementaryAbelian 2 D := hD
  have hKH : K ≤ H := (map_subtype_le (pResidual 2 (H ⊓ centralizer ({i} : Set G) : Subgroup G))).trans inf_le_left
  have hKi : K ≤ centralizer ({i} : Set G) :=
    (map_subtype_le (pResidual 2 (H ⊓ centralizer ({i} : Set G) : Subgroup G))).trans inf_le_right
  have hUH : U ≤ H := hUcore ▸ pCoreIn_le 2 H
  have hHU : H ≤ normalizer (U : Set G) := by
    rw [← hUcore]
    exact H.le_normalizer.trans (normalizer_le_normalizer_characteristic_image H (pCore 2 H))
  have hDH : D ≤ H := by
    intro d hd
    exact mem_centralizer_singleton_iff.mpr
      ((D.le_centralizer hd) z (mem_sup_right (mem_zpowers z))).symm
  have hJH : J ≤ H := sup_le (sup_le hKH hUH) hDH
  have hKD : K ⊔ U ≤ normalizer (D : Set G) :=
    lift_normalized_by_residual_join_core U K z i hZ hiU (hKH.trans hHU) hKi hmoved
  have hJD : J ≤ normalizer (D : Set G) := sup_le hKD D.le_normalizer
  apply le_antisymm
  · have hbound := core_le_join_of_quotient_core_le H J ⟨i,hiz⟩ hJH hbar
    rw [hUcore] at hbound
    exact hbound.trans (sup_le_sup_left
      (show zpowers i ≤ D from le_sup_right.trans le_sup_left) U)
  · apply le_pCoreIn_of_normalizes
      ((IsExtraspecial.isPGroup 2 U).to_sup_of_normal_right'
        (IsElementaryAbelian.isPGroup 2 D) (le_sup_right.trans hKD))
      (sup_le (le_sup_right.trans le_sup_left) le_sup_right)
    exact (le_inf (hJH.trans hHU) hJD).trans
      (U.normalizer_inf_normalizer_le_normalizer_sup D)


omit [Finite G] in
/-- The joint centralizer is literally C_G(⟨z,i⟩). -/
theorem joint_centralizer_eq (z i : G) :
    centralizer ((zpowers z ⊔ zpowers i : Subgroup G) : Set G) =
      centralizer ({z} : Set G) ⊓ centralizer ({i} : Set G) := by
  apply le_antisymm
  · exact le_inf
      (centralizer_le (Set.singleton_subset_iff.mpr (mem_sup_left (mem_zpowers z))))
      (centralizer_le (Set.singleton_subset_iff.mpr (mem_sup_right (mem_zpowers i))))
  · apply le_centralizer_iff.mpr
    apply sup_le
    · apply le_centralizer_iff.mpr
      simpa only [zpowers_eq_closure, centralizer_closure] using
        (inf_le_left : centralizer ({z} : Set G) ⊓ centralizer ({i} : Set G) ≤
          centralizer ({z} : Set G))
    · apply le_centralizer_iff.mpr
      simpa only [zpowers_eq_closure, centralizer_closure] using
        (inf_le_right : centralizer ({z} : Set G) ⊓ centralizer ({i} : Set G) ≤
          centralizer ({i} : Set G))

end CFSG.Quasithin.Chapter14.Section04.LargerDimension.Orthogonal
