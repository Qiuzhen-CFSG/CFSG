module
public import Theory.SpecificGroups.Janko4.Model.InvolutionCentralizers.NormalElementary
public import Theory.SpecificGroups.Janko4.Model.InvolutionCentralizers.Second.ResidualCore
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.Mathieu.ResidualGeneration
public import Theory.GroupTheory.PGroup.NormalChain
public import Theory.GroupTheory.CComponent.QuotientLifting

/-!
# Large elementary subgroups normalized by the second J₄ residual

The quotient of the full involution centralizer by its perfect residual is a
2-group. An elementary 2-subgroup normalized by that residual is therefore
subnormal and lies in the full two-core. If its order is at least 1024 and it
contains a nonidentity central element, the native order-eleven obstruction
excludes order 1024. It is consequently the entire order-2048 core.

Source: Aschbacher–Smith, 4.4.3, printed p.623; GLS3 Table 5.3i.
The native centralizer and module calculations retain their ATLAS attribution
through the imported second-centralizer modules.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace Janko4.InvolutionCentralizers
attribute [local irreducible] modelGroup matrixA matrixB

private theorem normalized_by_residual_le_core {C : Type*} [Group C] [Finite C]
    (W : Subgroup C) (hW : IsPGroup 2 W)
    (hn : solvableResidual C ≤ normalizer (W : Set C))
    (hQ : IsPGroup 2 (C ⧸ solvableResidual C)) : W ≤ pCore 2 C := by
  let R := solvableResidual C
  let H := R ⊔ W
  let q := QuotientGroup.mk' R
  have hs : H.IsSubnormal := by
    have hh := (hQ.subgroup_isSubnormal (H.map q)).comap q
    simpa only [comap_map_eq,q,QuotientGroup.ker_mk',sup_of_le_left (show R ≤ H from le_sup_left)] using hh
  let U := W.subgroupOf H
  let : U.Normal := normal_subgroupOf_of_le_normalizer (sup_le hn W.le_normalizer)
  have hu : U ≤ pCore 2 H := le_sSup ⟨inferInstance,hW.comap_subtype⟩
  have hm := map_mono (f := H.subtype) hu
  rw [map_subgroupOf_eq_of_le (show W ≤ H from le_sup_right)] at hm
  exact hm.trans (pCoreIn_le_of_subnormal 2 hs)

namespace Second
/-- The native elementary kernel is the full two-core. -/
theorem ambient_twoCore_eq_kernel : pCore 2 ambientCentralizer = ambientKernel := by
  open Sporadic.Mathieu in
  have hbase : pCore 2 M22 = ⊥ := by
    let := m22_isSimpleGroup
    rcases (inferInstance : (pCore 2 M22).Normal).eq_bot_or_eq_top with hb | ht
    · exact hb
    · have hp : IsPGroup 2 M22 := by
        have hh : IsPGroup 2 (⊤ : Subgroup M22) := ht ▸ pCore_isPGroup
        exact hh.of_surjective (Subgroup.topEquiv (G := M22)).toMonoidHom Subgroup.topEquiv.surjective
      obtain ⟨k,hk⟩ := hp.exists_card_eq
      have hd : 11 ∣ Nat.card M22 := by rw [m22_order]; decide
      rw [hk] at hd
      have hh := (show Nat.Prime 11 by decide).dvd_of_dvd_pow hd
      norm_num at hh
  exact core_eq_kernel_of_action 2
    (conj_injective_of_center_eq_bot Sporadic.Mathieu.m22_center_eq_bot) hbase
    ambientExtension.rightHom
    (fun x => ambientExtension.rightHom_surjective (MulAut.conj x))
    (by let := ambientKernel_elementary; exact IsElementaryAbelian.isPGroup 2 _)

private theorem kernel_le_residual : ambientKernel ≤ solvableResidual ambientCentralizer := by
  have hlocal : kernel ≤ solvableResidual localCentralizer := by
    rw [←CoreMovement.kernel_fully_moved]
    exact commutator_le_right _ _
  rw [ambientKernel_eq_map,←map_solvableResidual_eq ambientEquivLocal.symm.toMonoidHom
    ambientEquivLocal.symm.surjective]
  exact map_mono hlocal

/-- Residual normalization and the original central element identify the full core. -/
theorem residual_normalized_large_elementary_eq_kernel
    (W : Subgroup ambientCentralizer) [IsElementaryAbelian 2 W]
    (hlarge : 1024 ≤ Nat.card W)
    (hn : solvableResidual ambientCentralizer ≤ normalizer (W : Set ambientCentralizer))
    (z : ambientCentralizer) (hz : z ∈ W) (hzne : z ≠ 1)
    (hzc : z ∈ center ambientCentralizer) : W = ambientKernel := by
  have hQ : IsPGroup 2 (ambientCentralizer ⧸ solvableResidual ambientCentralizer) := by
    have he := LocalStructure.involution_centralizer_residuals
      (seed : Model) seed_order
    change pResidual 2 ambientCentralizer = solvableResidual ambientCentralizer at he
    exact (isPGroup_quotient_pResidual (G := ambientCentralizer) 2).of_equiv
      (QuotientGroup.quotientMulEquivOfEq he)
  have hWQ : W ≤ ambientKernel := by
    rw [←ambient_twoCore_eq_kernel]
    exact normalized_by_residual_le_core W (IsElementaryAbelian.isPGroup 2 W) hn hQ
  have hupper := card_le_of_le hWQ
  rw [ambientKernel_card] at hupper
  obtain ⟨n,hnc⟩ := (IsElementaryAbelian.isPGroup 2 W).exists_card_eq
  have hbound : n ≤ 11 := by
    by_contra! hh
    have hp := Nat.pow_le_pow_right (by decide : 0 < 2) hh
    norm_num at hp
    omega
  have hcards : Nat.card W = 1024 ∨ Nat.card W = 2048 := by
    rw [hnc] at hlarge hupper ⊢
    interval_cases n <;> norm_num at *
  rcases hcards with hcard | hcard
  · exact (second_no_elementary_large_normalized (solvableResidual ambientCentralizer) W hQ
      (hWQ.trans kernel_le_residual) hn (.inr hcard) z hz hzne hzc).elim
  · exact eq_of_le_of_card_ge hWQ (by rw [hcard,ambientKernel_card])
end Second
end Janko4.InvolutionCentralizers
