module
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.Recognition.FactorAutomizers

public import Theory.GroupTheory.ElementaryEightFixedPointDihedral

/-! An actual H-overgroup of A with order 384 and two-core intersection
contained in U induces S₄ on A. Restriction to A∩U has kernel A and fixes Z.
The consumer is J=R O²(N_H(A)), with residual geometry supplied separately.
Source: Aschbacher–Smith 14.3.19. -/

@[expose] public noncomputable section
open Subgroup Module Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section03.NonabelianSource.Recognition
open Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter12.Section08.InvariantFlag.Symplectic
open Chapter14.Section02 SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
variable {G:Type*} [Group G] [Finite G]

theorem factor_overgroup_centralizer_of_full_orthogonal
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
    (J:Subgroup G) (hAJ:A≤J) (hJH:J≤F.H) (hJU:J⊓F.H.pCoreIn 2≤F.U) :
    J⊓centralizer ((A⊓F.U:Subgroup G):Set G)=A := by
  let Q:=F.H.pCoreIn 2
  let C:=A⊓F.U
  let q:=QuotientGroup.mk' F.terminalHatAction.ker
  have hAH:A≤F.H := hAJ.trans hJH
  have hAC:A≤centralizer (C:Set G) := by
    intro a ha c hc
    exact congrArg Subtype.val (mul_comm (⟨c,hc.1⟩:A) ⟨a,ha⟩)
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
theorem factor_overgroup_symmetric_automizer_of_full_orthogonal
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
    (J:Subgroup G) (hAJ:A≤J) (hJH:J≤F.H) (hJU:J⊓F.H.pCoreIn 2≤F.U)
    (hJcard:Nat.card J=384) (hJA:J≤normalizer (A:Set G)) :
    Nat.card (A.normalizerMonoidHom.comp (inclusion hJA)).range=24 ∧
    Nonempty ((A.normalizerMonoidHom.comp (inclusion hJA)).range ≃* Equiv.Perm (Fin 4)) := by
  let C:=A⊓F.U
  have hJC:J≤normalizer (C:Set G) :=
    (le_inf hJA (hJH.trans (le_normalizer_conjugateSpanBy _ _))).trans
      inf_normalizer_le_normalizer_inf
  have hcent:J⊓centralizer (C:Set G)=A :=
    factor_overgroup_centralizer_of_full_orthogonal
      hG T hempty hM hu hmany hcard e hnot F dg hZ hne g hgP hgH hr A hAR hVA hAc hc8 J hAJ hJH hJU
  have hcentA:J⊓centralizer (A:Set G)=A := by
    apply le_antisymm
    · exact (inf_le_inf_left J (centralizer_le (show (C:Set G)⊆A from inf_le_left))).trans hcent.le
    · exact le_inf hAJ A.le_centralizer
  let f:=A.normalizerMonoidHom.comp (inclusion hJA)
  let k:=C.normalizerMonoidHom.comp (inclusion hJC)
  have hfker:f.ker=A.subgroupOf J := by
    ext x
    change inclusion hJA x∈A.normalizerMonoidHom.ker ↔ (x:G)∈A
    rw [normalizerMonoidHom_ker]
    change (x:G)∈centralizer (A:Set G) ↔ (x:G)∈A
    conv_rhs => rw [←hcentA]
    have hxJ:(x:G)∈J := x.property
    simp only [mem_inf,hxJ,true_and]
  have hkker:k.ker=A.subgroupOf J := by
    ext x
    change inclusion hJC x∈C.normalizerMonoidHom.ker ↔ (x:G)∈A
    rw [normalizerMonoidHom_ker]
    change (x:G)∈centralizer (C:Set G) ↔ (x:G)∈A
    conv_rhs => rw [←hcent]
    have hxJ:(x:G)∈J := x.property
    simp only [mem_inf,hxJ,true_and]
  have hkcard:Nat.card k.range=24 := by
    have hh:=k.ker.index_mul_card
    rw [index_ker,hkker,Nat.card_congr (subgroupOfEquivOfLe hAJ).toEquiv,hAc,hJcard] at hh
    omega
  let r:f.range≃*k.range := (QuotientGroup.quotientKerEquivRange f).symm.trans
    ((QuotientGroup.quotientMulEquivOfEq (hfker.trans hkker.symm)).trans
      (QuotientGroup.quotientKerEquivRange k))
  refine ⟨(Nat.card_congr r.toEquiv).trans hkcard,?_⟩
  let : IsElementaryAbelian 2 C := IsElementaryAbelian.of_injective
    (inclusion (show C≤A from inf_le_left)) (inclusion_injective _)
  have hzcard:Nat.card (F.Vi 1)=2 := by simpa using F.card 1 (by omega)
  obtain ⟨z,hz,_⟩ := (Nat.card_eq_two_iff' (1:F.Vi 1)).mp hzcard
  have hzA:(z:G)∈A := ((F.le_seed 1).trans hVA) z.property
  have hzU:(z:G)∈F.U := ((F.le_seed 1).trans (le_conjugateSpanBy _ _)) z.property
  let zC:C:=⟨z,⟨hzA,hzU⟩⟩
  have hzC:zC≠1 := fun hh=>hz (Subtype.ext (congrArg (fun w:C=>(w:G)) hh))
  have hfix:∀a:k.range,(a:MulAut C) zC=zC := by
    rintro ⟨a,⟨x,rfl⟩⟩
    apply Subtype.ext
    change (x:G)*(z:G)*(x:G)⁻¹=(z:G)
    have hx:(x:G)∈centralizer (F.Vi 1:Set G) :=
      normalizer_le_centralizer_of_card_two (F.Vi 1) hzcard (hJH x.property)
    rw [←hx z z.property,mul_inv_cancel_right]
  obtain ⟨d⟩ := elementaryEight_fixed_point_order24_equiv_S4 hc8 zC hzC k.range hkcard hfix
  exact ⟨r.trans d⟩
theorem factor_residual_normalizer_symmetric_automizer
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
    (hRA:(F.I₂ (sourceResidual M Mc)).pCoreIn 2≤normalizer (A:Set G)) :
    let N:=F.H⊓normalizer (A:Set G)
    let Y:=(pResidual 2 N).map N.subtype
    let J:=(F.I₂ (sourceResidual M Mc)).pCoreIn 2⊔Y
    J⊓F.H.pCoreIn 2≤F.U → Nat.card J=384 →
      ∃hJA:J≤normalizer (A:Set G),
        Nat.card (A.normalizerMonoidHom.comp (inclusion hJA)).range=24 ∧
        Nonempty ((A.normalizerMonoidHom.comp (inclusion hJA)).range ≃* Equiv.Perm (Fin 4)) := by
  intro N Y J hJU hJcard
  have hRT:(F.I₂ (sourceResidual M Mc)).pCoreIn 2≤(T:Subgroup G) :=
    (parabolic_core_sylow_index_of_full_orthogonal
      hG T hempty hM hu hmany hcard e hnot F dg hZ hne g hgP hgH hr).1
  have hYN:Y≤N:=map_subtype_le _
  have hJH:J≤F.H := sup_le (hRT.trans (F.invariant 1)) (hYN.trans inf_le_left)
  have hJA:J≤normalizer (A:Set G) := sup_le hRA (hYN.trans inf_le_right)
  exact ⟨hJA,factor_overgroup_symmetric_automizer_of_full_orthogonal
    hG T hempty hM hu hmany hcard e hnot F dg hZ hne g hgP hgH hr A hAR hVA hAc hc8
    J (hAR.trans le_sup_left) hJH hJU hJcard hJA⟩
end CFSG.Quasithin.Chapter14.Section03.NonabelianSource.Recognition
