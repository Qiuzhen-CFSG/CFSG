module
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.Recognition.FactorAutomizersCentralizer
public import Theory.GroupTheory.QuaternionElementaryEightCentralizer

/-! Restriction of the RU action to the factor eight has kernel precisely A.
The terminal pointwise stabilizer reduces the kernel to AU, and the quaternion
self-centralizer of the eight finishes the calculation. Source: 14.3.19. -/

@[expose] public noncomputable section
open Subgroup Module Theory.GroupTheory
open scoped IsMulCommutative Pointwise
namespace CFSG.Quasithin.Chapter14.Section03.NonabelianSource.Recognition
open Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter12.Section08.InvariantFlag.Symplectic
open Chapter14.Section02 SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
variable {G:Type*} [Group G] [Finite G]

theorem elementary_factor_join_centralizer_of_full_orthogonal
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (hnot : ¬ ClassificationModels.IsTheoremEModel G)
    (F : InvariantFlag T (rankTwoSeed T M) 2)
    [IsElementaryAbelian 2 (rankTwoSeed T M)] [IsElementaryAbelian 2 F.Uhat]
    (dg : ClosureGeometry F) (hZ : F.ZU=F.Vi 1) (hne : ¬ IsMulCommutative F.U)
    (g : G) (hgP : g∈F.P (sourceResidual M Mc)) (hgH : g∉F.H)
    (hr : ChapterG.Section09.FittingRecognition.OrthogonalRealization F.terminalRepresentation ⊤)
    (A:Subgroup G) [IsElementaryAbelian 2 A]
    (hAR:A≤(F.I₂ (sourceResidual M Mc)).pCoreIn 2)
    (hVA:rankTwoSeed T M≤A) (hAc:Nat.card A=16)
    (hc8:Nat.card (A⊓F.U:Subgroup G)=8) :
    (((F.I₂ (sourceResidual M Mc)).pCoreIn 2⊔F.U)⊓
      centralizer ((A⊓F.U:Subgroup G):Set G):Subgroup G)=A := by
  let R:=(F.I₂ (sourceResidual M Mc)).pCoreIn 2
  let Q:=F.H.pCoreIn 2
  let J:=R⊔F.U
  let C:=A⊓F.U
  let q:=QuotientGroup.mk' F.terminalHatAction.ker
  have hRT:R≤(T:Subgroup G) := (parabolic_core_sylow_index_of_full_orthogonal
    hG T hempty hM hu hmany hcard e hnot F dg hZ hne g hgP hgH hr).1
  have hRH:R≤F.H := hRT.trans (F.invariant 1)
  have hJH:J≤F.H := sup_le hRH F.U_le_H
  have hAH:A≤F.H := hAR.trans hRH
  have hAJ:A≤J := hAR.trans le_sup_left
  have hAC:A≤centralizer (C:Set G) := by
    intro a ha c hc
    exact congrArg Subtype.val (mul_comm (⟨c,hc.1⟩:A) ⟨a,ha⟩)
  have hUQ:F.U≤Q := le_pCoreIn_of_normalizes dg.two F.U_le_H
    (le_normalizer_conjugateSpanBy _ _)
  have hRQ:R⊓Q=F.W := (parabolic_core_intersection_of_full_orthogonal
    hG T hempty hM hu hmany hcard e hnot F dg hZ hne g hgP hgH hr).1
  have hJU:J⊓Q≤F.U := by
    rintro x ⟨hx,hxQ⟩
    have hx':x∈(R:Set G)*(F.U:Set G) := by
      rw [←coe_mul_of_left_le_normalizer_right R F.U
        (hRH.trans (le_normalizer_conjugateSpanBy _ _))]
      exact hx
    obtain ⟨r,hrR,u,huU,he⟩ := hx'
    change r*u=x at he
    have hrQ:r∈Q := by
      have hh:=Q.mul_mem hxQ (Q.inv_mem (hUQ huU))
      rw [←he,mul_inv_cancel_right] at hh
      exact hh
    have hrU:r∈F.U := (show r∈F.W from hRQ ▸ ⟨hrR,hrQ⟩).1
    exact he ▸ F.U.mul_mem hrU huU
  let : IsElementaryAbelian 2 C := IsElementaryAbelian.of_injective
    (inclusion (show C≤A from inf_le_left)) (inclusion_injective _)
  let E:=C.subgroupOf F.U
  let : IsElementaryAbelian 2 E := IsElementaryAbelian.subgroupOf (show C≤F.U from inf_le_right)
  obtain ⟨dU⟩ := quaternion_closure_of_full_orthogonal F dg hZ hne hr
  have hE:Nat.card E=8 :=
    (Nat.card_congr (subgroupOfEquivOfLe (show C≤F.U from inf_le_right)).toEquiv).trans hc8
  have hEC:centralizer (E:Set F.U)=E := by
    have hh:=inf_centralizer_elementary_eight_of_quaternion_factors dU.left dU.right E
      dU.left_model dU.right_model dU.intersection_card dU.commute hE (dU.span ▸ le_top)
    simpa only [dU.span,top_inf_eq] using hh
  have hUC:F.U⊓centralizer (C:Set G)≤C := by
    rintro x ⟨hxU,hxc⟩
    have hh:(⟨x,hxU⟩:F.U)∈centralizer (E:Set F.U) := by
      intro u hu
      exact Subtype.ext (hxc u hu)
    change (⟨x,hxU⟩:F.U)∈E
    exact hEC ▸ hh
  have hnotAU:¬A≤F.U := by
    intro hh
    rw [inf_eq_left.mpr hh,hAc] at hc8
    contradiction
  obtain ⟨a,ha,haU⟩:=SetLike.not_le_iff_exists.mp hnotAU
  have hsmall (x:G) (hxJ:x∈J) (hxc:x∈centralizer (C:Set G))
      (hxq:q ⟨x,hJH hxJ⟩=1) : x∈A := by
    have hxK:(⟨x,hJH hxJ⟩:F.H)∈F.terminalHatAction.ker :=
      (QuotientGroup.eq_one_iff _).mp hxq
    rw [terminal_kernel_of_center_point F dg hZ] at hxK
    have hxQ:x∈Q := mem_map_of_mem F.H.subtype hxK
    exact (hUC ⟨hJU ⟨hxJ,hxQ⟩,hxc⟩).1
  apply le_antisymm
  · rintro x ⟨hxJ,hxc⟩
    rcases elementary_factor_pointwise_terminal_stabilizer
      hG T hempty hM hu hmany hcard e hnot F dg hZ hne g hgP hgH hr
      A hAR hAH hVA hc8 a ha haU ⟨x,hJH hxJ⟩
      (fun u hu=>(hxc (u:G) ⟨hu,u.property⟩).symm) with hxq | hxq
    · exact hsmall x hxJ hxc hxq
    · have hyJ:a⁻¹*x∈J := J.mul_mem (J.inv_mem (hAJ ha)) hxJ
      have hyc:a⁻¹*x∈centralizer (C:Set G) :=
        (centralizer (C:Set G)).mul_mem ((centralizer (C:Set G)).inv_mem (hAC ha)) hxc
      have hyq:q ⟨a⁻¹*x,hJH hyJ⟩=1 := by
        change q ((⟨a,hAH ha⟩:F.H)⁻¹*⟨x,hJH hxJ⟩)=1
        rw [map_mul,map_inv,hxq,inv_mul_cancel]
      have hyA:=hsmall (a⁻¹*x) hyJ hyc hyq
      have hh:=A.mul_mem ha hyA
      simpa only [mul_inv_cancel_left] using hh
  · exact le_inf hAJ hAC
theorem factor_join_order_of_full_orthogonal
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (hnot : ¬ ClassificationModels.IsTheoremEModel G)
    (F : InvariantFlag T (rankTwoSeed T M) 2)
    [IsElementaryAbelian 2 (rankTwoSeed T M)] [IsElementaryAbelian 2 F.Uhat]
    (dg : ClosureGeometry F) (hZ : F.ZU=F.Vi 1) (hne : ¬ IsMulCommutative F.U)
    (g : G) (hgP : g∈F.P (sourceResidual M Mc)) (hgH : g∉F.H)
    (hr : ChapterG.Section09.FittingRecognition.OrthogonalRealization F.terminalRepresentation ⊤) :
    Nat.card ((F.I₂ (sourceResidual M Mc)).pCoreIn 2⊔F.U:Subgroup G)=128 := by
  let R:=(F.I₂ (sourceResidual M Mc)).pCoreIn 2
  let Q:=F.H.pCoreIn 2
  let J:=R⊔F.U
  let q:=QuotientGroup.mk' F.terminalHatAction.ker
  have hRT:R≤(T:Subgroup G) := (parabolic_core_sylow_index_of_full_orthogonal
    hG T hempty hM hu hmany hcard e hnot F dg hZ hne g hgP hgH hr).1
  have hRH:R≤F.H := hRT.trans (F.invariant 1)
  have hJH:J≤F.H := sup_le hRH F.U_le_H
  have hUQ:F.U≤Q := le_pCoreIn_of_normalizes dg.two F.U_le_H
    (le_normalizer_conjugateSpanBy _ _)
  have hRQ:R⊓Q=F.W := (parabolic_core_intersection_of_full_orthogonal
    hG T hempty hM hu hmany hcard e hnot F dg hZ hne g hgP hgH hr).1
  have hJU:J⊓Q≤F.U := by
    rintro x ⟨hx,hxQ⟩
    have hx':x∈(R:Set G)*(F.U:Set G) := by
      rw [←coe_mul_of_left_le_normalizer_right R F.U
        (hRH.trans (le_normalizer_conjugateSpanBy _ _))]
      exact hx
    obtain ⟨r,hrR,u,huU,he⟩ := hx'
    change r*u=x at he
    have hrQ:r∈Q := by
      have hh:=Q.mul_mem hxQ (Q.inv_mem (hUQ huU))
      rw [←he,mul_inv_cancel_right] at hh
      exact hh
    have hrU:r∈F.U := (show r∈F.W from hRQ ▸ ⟨hrR,hrQ⟩).1
    exact he ▸ F.U.mul_mem hrU huU
  have hJQ:J⊓Q=F.U := le_antisymm hJU (le_inf le_sup_right hUQ)
  have hqker:q.ker=pCore 2 F.H := by
    rw [QuotientGroup.ker_mk',terminal_kernel_of_center_point F dg hZ]
  have hUdot:F.terminalDot F.U=⊥ := by
    apply (Subgroup.map_eq_bot_iff _).mpr
    rw [hqker]
    intro u hu
    obtain ⟨v,hv,he⟩ := hUQ hu
    exact (show v=u from Subtype.ext he) ▸ hv
  have hJdot:Nat.card (F.terminalDot J)=4 := by
    change Nat.card (((R⊔F.U).subgroupOf F.H).map q)=4
    rw [subgroupOf_sup hRH F.U_le_H,Subgroup.map_sup]
    change Nat.card (F.terminalDot R⊔F.terminalDot F.U:Subgroup F.TerminalHdot)=4
    rw [hUdot,sup_bot_eq]
    exact (parabolic_core_intersection_of_full_orthogonal
      hG T hempty hM hu hmany hcard e hnot F dg hZ hne g hgP hgH hr).2.2.2.2
  have hind:F.U.relIndex J=4 := by
    change Nat.card ((J.subgroupOf F.H).map q)=4 at hJdot
    rw [←relIndex_ker _ q,hqker] at hJdot
    have he:=relIndex_map_map_of_injective (pCore 2 F.H) (J.subgroupOf F.H) F.H.subtype_injective
    rw [map_subgroupOf_eq_of_le hJH] at he
    change Q.relIndex J=(pCore 2 F.H).relIndex (J.subgroupOf F.H) at he
    rw [←he,←inf_relIndex_right,inf_comm Q J,hJQ] at hJdot
    exact hJdot
  obtain ⟨dU⟩ := quaternion_closure_of_full_orthogonal F dg hZ hne hr
  have hh:=relIndex_mul_card_of_le (show F.U≤J from le_sup_right)
  rw [hind,dU.card] at hh
  exact hh.symm
end CFSG.Quasithin.Chapter14.Section03.NonabelianSource.Recognition
