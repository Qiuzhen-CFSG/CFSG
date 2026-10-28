module
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.Recognition.FactorAutomizersKernel

public import Theory.GroupTheory.ElementaryEightFixedPointDihedral

/-! The literal automizer induced by RU on its chosen elementary sixteen is
dihedral of order eight. Restriction to A∩U has the same kernel A and fixes
the marked central point, giving a Sylow subgroup of S₄. Source: 14.3.19. -/

@[expose] public noncomputable section
open Subgroup Module Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section03.NonabelianSource.Recognition
open Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter12.Section08.InvariantFlag.Symplectic
open Chapter14.Section02 SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
variable {G:Type*} [Group G] [Finite G]

theorem factor_join_dihedral_automizer_of_full_orthogonal
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
    (hJA:(F.I₂ (sourceResidual M Mc)).pCoreIn 2⊔F.U≤normalizer (A:Set G)) :
    Nat.card (A.normalizerMonoidHom.comp (inclusion hJA)).range=8 ∧
    Nonempty ((A.normalizerMonoidHom.comp (inclusion hJA)).range ≃* DihedralGroup 4) := by
  let R:=(F.I₂ (sourceResidual M Mc)).pCoreIn 2
  let J:=R⊔F.U
  let C:=A⊓F.U
  have hRT:R≤(T:Subgroup G) := (parabolic_core_sylow_index_of_full_orthogonal
    hG T hempty hM hu hmany hcard e hnot F dg hZ hne g hgP hgH hr).1
  have hJH:J≤F.H := sup_le (hRT.trans (F.invariant 1)) F.U_le_H
  have hAJ:A≤J := hAR.trans le_sup_left
  have hJC:J≤normalizer (C:Set G) :=
    (le_inf hJA (hJH.trans (le_normalizer_conjugateSpanBy _ _))).trans
      inf_normalizer_le_normalizer_inf
  have hcent:J⊓centralizer (C:Set G)=A :=
    elementary_factor_join_centralizer_of_full_orthogonal
      hG T hempty hM hu hmany hcard e hnot F dg hZ hne g hgP hgH hr A hAR hVA hAc hc8
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
  have hJcard:Nat.card J=128 := factor_join_order_of_full_orthogonal
    hG T hempty hM hu hmany hcard e hnot F dg hZ hne g hgP hgH hr
  have hkcard:Nat.card k.range=8 := by
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
  obtain ⟨d⟩ := elementaryEight_fixed_point_order8_equiv_D8 hc8 zC hzC k.range hkcard hfix
  exact ⟨r.trans d⟩
theorem factor_pair_dihedral_automizers_of_full_orthogonal
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
    (hAN:F.I₂ (sourceResidual M Mc)⊔F.H.pCoreIn 2≤normalizer (A:Set G))
    (hBN:F.I₂ (sourceResidual M Mc)⊔F.H.pCoreIn 2≤normalizer (B:Set G))
    (hmax:∀E:Subgroup G,IsElementaryAbelian 2 E→
      E≤(F.I₂ (sourceResidual M Mc)).pCoreIn 2→E≤A∨E≤B) :
    ∃(hJA:(F.I₂ (sourceResidual M Mc)).pCoreIn 2⊔F.U≤normalizer (A:Set G))
      (hJB:(F.I₂ (sourceResidual M Mc)).pCoreIn 2⊔F.U≤normalizer (B:Set G)),
      Nonempty ((A.normalizerMonoidHom.comp (inclusion hJA)).range ≃* DihedralGroup 4) ∧
      Nonempty ((B.normalizerMonoidHom.comp (inclusion hJB)).range ≃* DihedralGroup 4) ∧
      IsPGroup 2 (F.H⊓centralizer (A:Set G):Subgroup G) ∧
      IsPGroup 2 (F.H⊓centralizer (B:Set G):Subgroup G) := by
  obtain ⟨ha8,hb8⟩:=elementary_factor_core_intersections_of_full_orthogonal
    hG T hempty hM hu hmany hcard e hnot F dg hZ hne g hgP hgH hr
    A B hAR hBR hVA hVB inferInstance inferInstance hmax
  have hUQ:F.U≤F.H.pCoreIn 2 := le_pCoreIn_of_normalizes dg.two F.U_le_H
    (le_normalizer_conjugateSpanBy _ _)
  have hJ:(F.I₂ (sourceResidual M Mc)).pCoreIn 2⊔F.U≤F.I₂ (sourceResidual M Mc)⊔F.H.pCoreIn 2 :=
    sup_le_sup (pCoreIn_le 2 _) hUQ
  let hJA:=hJ.trans hAN
  let hJB:=hJ.trans hBN
  exact ⟨hJA,hJB,
    (factor_join_dihedral_automizer_of_full_orthogonal
      hG T hempty hM hu hmany hcard e hnot F dg hZ hne g hgP hgH hr A hAR hVA hAc ha8 hJA).2,
    (factor_join_dihedral_automizer_of_full_orthogonal
      hG T hempty hM hu hmany hcard e hnot F dg hZ hne g hgP hgH hr B hBR hVB hBc hb8 hJB).2,
    (elementary_factor_centralizer_twoGroup_of_full_orthogonal
      hG T hempty hM hu hmany hcard e hnot F dg hZ hne g hgP hgH hr A hAR hVA hAc ha8).2,
    (elementary_factor_centralizer_twoGroup_of_full_orthogonal
      hG T hempty hM hu hmany hcard e hnot F dg hZ hne g hgP hgH hr B hBR hVB hBc hb8).2⟩
end CFSG.Quasithin.Chapter14.Section03.NonabelianSource.Recognition
