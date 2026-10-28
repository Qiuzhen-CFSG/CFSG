module
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.Recognition.ParabolicNormalizerFixedPlane
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.Recognition.ParabolicNormalizerCore
public import Theory.GroupTheory.ElementaryFactorOutsideInvolutions
public import Theory.GroupTheory.PResidual.TwelveNormalizerImage
public import Theory.GroupTheory.PCoreRestriction

/-! The original elementary factor has dotted normalizer exactly its dotted
centralizer, a C₂×S₃. Its singular plane detects outside involutions in AU,
so A is the unique elementary sixteen in AU. The residual of the centralizer
preimage normalizes AU and hence A. Its image supplies the factor three,
while the original parabolic core supplies the factor four.
Source:Aschbacher–Smith14.3.18(6), printed p.996. -/

@[expose] public noncomputable section
open Subgroup Module Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section03.NonabelianSource.Recognition
open Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter12.Section08.InvariantFlag.Symplectic
open Chapter14.Section02 SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
variable {G:Type*} [Group G] [Finite G]

theorem elementary_factor_normalizer_of_full_orthogonal
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
    (hc8:Nat.card (A⊓F.U:Subgroup G)=8)
    (hNA:(F.I₂ (sourceResidual M Mc)).pCoreIn 2≤normalizer (A:Set G)) :
    F.terminalDot (F.H⊓normalizer (A:Set G))=centralizer (F.terminalDot A:Set F.TerminalHdot) ∧
    Nonempty (centralizer (F.terminalDot A:Set F.TerminalHdot) ≃*
      (Multiplicative (ZMod 2) × Equiv.Perm (Fin 3))) := by
  let R:=(F.I₂ (sourceResidual M Mc)).pCoreIn 2
  let Q:=F.H.pCoreIn 2
  let q:=QuotientGroup.mk' F.terminalHatAction.ker
  have hRT:R≤(T:Subgroup G) := (parabolic_core_sylow_index_of_full_orthogonal
    hG T hempty hM hu hmany hcard e hnot F dg hZ hne g hgP hgH hr).1
  have hRH:R≤F.H := hRT.trans (F.invariant 1)
  have hAH:A≤F.H := hAR.trans hRH
  have hAnU:A≤normalizer (F.U:Set G) := hAH.trans (le_normalizer_conjugateSpanBy _ _)
  obtain ⟨dU⟩ := quaternion_closure_of_full_orthogonal F dg hZ hne hr
  have hfix:∀a∈A,a∉F.U→∀u∈F.U,a*u*a⁻¹=u⁻¹→u∈A := by
    intro a ha haU u huU hi
    apply (elementary_factor_fixed_plane_of_full_orthogonal
      hG T hempty hM hu hmany hcard e hnot F dg hZ hne g hgP hgH hr
      A hAR hAH hVA hc8 a ha haU).1 ⟨u,huU⟩
    apply Additive.toMul.injective
    change F.terminalHatAction ⟨a,hAH ha⟩ (QuotientGroup.mk' (center F.U) ⟨u,huU⟩)=
      QuotientGroup.mk' (center F.U) ⟨u,huU⟩
    rw [F.terminalHatAction_apply_mk]
    have he:F.U.normalizerMonoidHom ⟨a,hAnU ha⟩ ⟨u,huU⟩=(⟨u,huU⟩:F.U)⁻¹ := Subtype.ext hi
    rw [he,map_inv]
    apply inv_eq_of_mul_eq_one_left
    have hh:=Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
      (IsElementaryAbelian.exponent_dvd_p 2 F.Uhat)
      (QuotientGroup.mk' (center F.U) (⟨u,huU⟩:F.U))
    simpa only [pow_two] using hh
  have hjoin:normalizer ((A⊔F.U:Subgroup G):Set G)≤normalizer (A:Set G) :=
    normalizer_join_le_of_outside_involutions F.U A dU hAc
      (outside_involution_mem_factor_of_inverse_bound F.U A hAnU hfix)
  obtain ⟨hRQ,_,_,_,hRdot⟩ := parabolic_core_intersection_of_full_orthogonal
    hG T hempty hM hu hmany hcard e hnot F dg hZ hne g hgP hgH hr
  have hUQ:F.U≤Q := le_pCoreIn_of_normalizes dg.two F.U_le_H
    (le_normalizer_conjugateSpanBy _ _)
  have hAQ:A⊓Q=A⊓F.U := by
    apply le_antisymm
    · exact le_inf inf_le_left (fun x hx=>(show x∈F.W from hRQ ▸ ⟨hAR hx.1,hx.2⟩).1)
    · exact inf_le_inf_left A hUQ
  have hqker:q.ker=pCore 2 F.H := by
    rw [QuotientGroup.ker_mk',terminal_kernel_of_center_point F dg hZ]
  have hAdot:Nat.card (F.terminalDot A)=2 := by
    change Nat.card ((A.subgroupOf F.H).map q)=2
    rw [←relIndex_ker _ q,hqker]
    have he:=relIndex_map_map_of_injective (pCore 2 F.H) (A.subgroupOf F.H) F.H.subtype_injective
    rw [map_subgroupOf_eq_of_le hAH] at he
    change Q.relIndex A=(pCore 2 F.H).relIndex (A.subgroupOf F.H) at he
    rw [←he,←inf_relIndex_right,inf_comm Q A,hAQ]
    have hh:=relIndex_mul_card_of_le (show A⊓F.U≤A from inf_le_left)
    rw [hc8,hAc] at hh
    omega
  have hnotAU:¬A≤F.U := by
    intro hh
    rw [inf_eq_left.mpr hh,hAc] at hc8
    contradiction
  obtain ⟨a,ha,haU⟩:=SetLike.not_le_iff_exists.mp hnotAU
  let aH:F.H:=⟨a,hAH ha⟩
  have haQ:a∉Q := fun hh=>haU ((hAQ ▸ (show a∈A⊓Q from ⟨ha,hh⟩)).2)
  have had:q aH≠1 := by
    intro hh
    have hk:aH∈F.terminalHatAction.ker := (QuotientGroup.eq_one_iff _).mp hh
    rw [terminal_kernel_of_center_point F dg hZ] at hk
    exact haQ (mem_map_of_mem F.H.subtype hk)
  have ha2:(q aH)^2=1 := by
    rw [←map_pow]
    have hh:aH^2=1 := Subtype.ext (elemPow_eq_one_of_isElementaryAbelian (p:=2) a ha)
    rw [hh,map_one]
  have hAz:zpowers (q aH)=F.terminalDot A := eq_of_le_of_card_ge
    (zpowers_le.mpr (mem_map_of_mem q (show aH∈A.subgroupOf F.H from ha)))
    (by rw [Nat.card_zpowers,orderOf_eq_prime ha2 had,hAdot])
  have hCeq:centralizer (F.terminalDot A:Set F.TerminalHdot)=
      centralizer ({q aH}:Set F.TerminalHdot) := by
    rw [←hAz,zpowers_eq_closure,centralizer_closure]
  have hmodel:Nonempty (centralizer (F.terminalDot A:Set F.TerminalHdot) ≃*
      (Multiplicative (ZMod 2) × Equiv.Perm (Fin 3))) := by
    rw [hCeq]
    exact (elementary_factor_fixed_plane_of_full_orthogonal
      hG T hempty hM hu hmany hcard e hnot F dg hZ hne g hgP hgH hr
      A hAR hAH hVA hc8 a ha haU).2
  obtain ⟨model⟩:=hmodel
  have hC12:Nat.card (centralizer (F.terminalDot A:Set F.TerminalHdot))=12 := by
    rw [Nat.card_congr model.toEquiv,Nat.card_prod]
    norm_num [Nat.card_eq_fintype_card,Fintype.card_perm,Nat.factorial]
  let UH:=F.U.subgroupOf F.H
  let AH:=A.subgroupOf F.H
  let RH:=R.subgroupOf F.H
  let : UH.Normal := (normal_subgroupOf_iff_le_normalizer F.U_le_H).mpr
    (le_normalizer_conjugateSpanBy _ _)
  have hres:pResidual 2 F.H⊓q.ker≤UH := by
    have hcore:=twoResidual_core_eq_U_of_full_orthogonal
      hG T hempty hM hu hmany hcard e hnot F dg hZ hne g hgP hgH hr
    intro x hx
    have hxQ:(x:G)∈Q := mem_map_of_mem F.H.subtype (hqker ▸ hx.2)
    have hxR:(x:G)∈(pResidual 2 F.H).map F.H.subtype := mem_map_of_mem F.H.subtype hx.1
    exact hcore.ge (inf_pCoreIn_le_of_le 2 (map_subtype_le _) ⟨hxR,hxQ⟩)
  have hjoinH:normalizer ((AH⊔UH:Subgroup F.H):Set F.H)≤normalizer (AH:Set F.H) := by
    rw [←subgroupOf_sup hAH F.U_le_H,←subgroupOf_normalizer_eq (sup_le hAH F.U_le_H),
      ←subgroupOf_normalizer_eq hAH]
    exact comap_mono hjoin
  have hRN:RH≤normalizer (AH:Set F.H) := by
    rw [←subgroupOf_normalizer_eq hAH]
    exact comap_mono hNA
  have heq:=normalizer_image_eq_twelve_centralizer q (QuotientGroup.mk'_surjective _)
    AH UH RH hres hjoinH hRN hRdot hAdot hC12
  refine ⟨?_,⟨model⟩⟩
  change ((F.H⊓normalizer (A:Set G)).subgroupOf F.H).map q=_
  rw [inf_subgroupOf_left,subgroupOf_normalizer_eq hAH]
  exact heq

/-- Source18(6) for the same two elementary factors supplied by source18(4).
The intersection orders are discharged here from the original factor census. -/
theorem elementary_factor_normalizers_of_full_orthogonal
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
    (A B:Subgroup G) [IsElementaryAbelian 2 A] [IsElementaryAbelian 2 B]
    (hAR:A≤(F.I₂ (sourceResidual M Mc)).pCoreIn 2)
    (hBR:B≤(F.I₂ (sourceResidual M Mc)).pCoreIn 2)
    (hVA:rankTwoSeed T M≤A) (hVB:rankTwoSeed T M≤B)
    (hAc:Nat.card A=16) (hBc:Nat.card B=16)
    (hNA:(F.I₂ (sourceResidual M Mc)).pCoreIn 2≤normalizer (A:Set G))
    (hNB:(F.I₂ (sourceResidual M Mc)).pCoreIn 2≤normalizer (B:Set G))
    (hmax:∀E:Subgroup G,IsElementaryAbelian 2 E→
      E≤(F.I₂ (sourceResidual M Mc)).pCoreIn 2→E≤A∨E≤B) :
    (F.terminalDot (F.H⊓normalizer (A:Set G))=centralizer (F.terminalDot A:Set F.TerminalHdot) ∧
      Nonempty (centralizer (F.terminalDot A:Set F.TerminalHdot) ≃*
        (Multiplicative (ZMod 2) × Equiv.Perm (Fin 3)))) ∧
    (F.terminalDot (F.H⊓normalizer (B:Set G))=centralizer (F.terminalDot B:Set F.TerminalHdot) ∧
      Nonempty (centralizer (F.terminalDot B:Set F.TerminalHdot) ≃*
        (Multiplicative (ZMod 2) × Equiv.Perm (Fin 3)))) := by
  obtain ⟨hAU,hBU⟩:=elementary_factor_core_intersections_of_full_orthogonal
    hG T hempty hM hu hmany hcard e hnot F dg hZ hne g hgP hgH hr
    A B hAR hBR hVA hVB inferInstance inferInstance hmax
  exact ⟨elementary_factor_normalizer_of_full_orthogonal
    hG T hempty hM hu hmany hcard e hnot F dg hZ hne g hgP hgH hr A hAR hVA hAc hAU hNA,
    elementary_factor_normalizer_of_full_orthogonal
    hG T hempty hM hu hmany hcard e hnot F dg hZ hne g hgP hgH hr B hBR hVB hBc hBU hNB⟩

end CFSG.Quasithin.Chapter14.Section03.NonabelianSource.Recognition
