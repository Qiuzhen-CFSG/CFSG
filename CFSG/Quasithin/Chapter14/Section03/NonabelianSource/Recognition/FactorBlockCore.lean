module
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.Recognition.FactorCoreQuotient
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.Recognition.FactorAutomizersKernel
public import Theory.SpecificGroups.AlternatingSix.SquareGeneratorKernel

/-!
# The elementary core and Sylow subgroup of the original A₆ block

For the actual residual join K=L O²(N_H(A)), the centralizer of A
normalizes O₂(L)=R. Thus its commutators with R lie in C_R(A)=A.
Normal generation by the nontrivial image of R makes the action kernel
central modulo A. The square-one quotient R/A excludes the double cover
of A₆, identifying the kernel, and hence O₂(K), with the chosen A.
The existing order-128 subgroup RU consequently has odd index 45 in K.

Source: Aschbacher–Smith, Quasithin Groups, 14.3.19(4), printed p.997.
-/

@[expose] public noncomputable section
open Subgroup Module Theory.GroupTheory
open scoped IsMulCommutative Pointwise commutatorElement
namespace CFSG.Quasithin.Chapter14.Section03.NonabelianSource.Recognition
open Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter14.Section02 SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
variable {G:Type*} [Group G] [Finite G]

private theorem factor_block_kernel_of_action
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
    (hVA:rankTwoSeed T M≤A) (hAc:Nat.card A=16)
    (hc8:Nat.card (A⊓F.U:Subgroup G)=8)
    (hAB:A⊔B=(F.I₂ (sourceResidual M Mc)).pCoreIn 2)
    (hRc:Nat.card ((F.I₂ (sourceResidual M Mc)).pCoreIn 2)=64)
    (hAN:F.I₂ (sourceResidual M Mc)⊔F.H.pCoreIn 2≤normalizer (A:Set G)) :
    let R := (F.I₂ (sourceResidual M Mc)).pCoreIn 2
    let N := F.H⊓normalizer (A:Set G)
    let Y := (pResidual 2 N).map N.subtype
    let K := sourceResidual M Mc⊔Y
    ∀hKA:K≤normalizer (A:Set G),
      (A.normalizerMonoidHom.comp (inclusion hKA)).range ≃* alternatingGroup (Fin 6) →
      K⊓centralizer (A:Set G)=A ∧ Nat.card K=5760 ∧
      ∃P:Sylow 2 K,(P:Subgroup K).map K.subtype=R⊔F.U := by
  intro R N Y K hKA eK
  let h := source_lemma_14_2_4 hG T hempty hM hu hmany hcard e
  obtain ⟨_,hKp,hSK,_⟩ := factor_generated_residual_geometry_of_full_orthogonal
    hG T hempty hM hu hmany hcard e hnot F dg hZ hne g hgP hgH hr A hAR hVA hAc hc8 hAN
  obtain ⟨_,hCp⟩ := factor_global_centralizer_twoGroup_of_full_orthogonal
    hG T hempty hM hu hmany hcard e hnot F dg hZ hne g hgP hgH hr A hAR hVA hAc hc8
  obtain ⟨_,_,hcore,_⟩ := parabolic_residual_core_structure_of_full_orthogonal
    hG T hempty hM hu hmany hcard e hnot F dg hZ hne g hgP hgH hr
  have hRK:R≤K := le_sup_left.trans hSK
  have hAK:A≤K := hAR.trans hRK
  have hcent:(R⊔F.U)⊓centralizer ((A⊓F.U:Subgroup G):Set G)=A :=
    elementary_factor_join_centralizer_of_full_orthogonal
      hG T hempty hM hu hmany hcard e hnot F dg hZ hne g hgP hgH hr A hAR hVA hAc hc8
  let C:=centralizer (A:Set G)
  have hRC:R⊓C=A := by
    apply le_antisymm
    · exact (inf_le_inf le_sup_left (centralizer_le (show (A⊓F.U:Subgroup G)≤A from inf_le_left))).trans hcent.le
    · exact le_inf hAR A.le_centralizer
  have hCM:C≤M := (centralizer_le hVA).trans h.seed_centralizer_le
  have hCL:C≤normalizer (sourceResidual M Mc:Set G) :=
    hCM.trans ((normal_subgroupOf_iff_le_normalizer (sourceResidual_le M Mc)).mp (residualY_normal M Mc))
  have hCR:C≤normalizer (R:Set G) := by
    change C≤normalizer ((F.I₂ (sourceResidual M Mc)).pCoreIn 2:Set G)
    rw [←hcore]
    exact hCL.trans (normalizer_le_normalizer_characteristic_image (sourceResidual M Mc) (pCore 2 _))
  have hcomm:⁅C,R⁆≤A := by
    rw [←hRC]
    exact le_inf (le_normalizer_iff_commutator_le_right.mp hCR)
      (le_normalizer_iff_commutator_le_left.mp
        ((hRK.trans hKA).trans (normalizer_le_normalizer_centralizer A)))
  have hsq:∀r∈R,r^2∈A := by
    intro r hrR
    have hBA:B≤normalizer (A:Set G) := hBR.trans (hRK.trans hKA)
    have hm:r∈(A:Set G)*(B:Set G) := by
      rw [←coe_mul_of_right_le_normalizer_left A B hBA,hAB]
      exact hrR
    obtain ⟨a,ha,b,hb,rfl⟩:=hm
    have hb2:b^2=1 := elemPow_eq_one_of_isElementaryAbelian (p:=2) b hb
    have hab:b*a*b⁻¹∈A := (mem_normalizer_iff.mp (hBA hb) a).mp ha
    have he:(a*b)^2=a*(b*a*b⁻¹)*b^2 := by simp only [pow_two];group
    rw [he,hb2,mul_one]
    exact A.mul_mem ha hab
  let φ:=A.normalizerMonoidHom.comp (inclusion hKA)
  let f:K→*alternatingGroup (Fin 6):=eK.toMonoidHom.comp φ.rangeRestrict
  have hf:Function.Surjective f:=eK.surjective.comp φ.rangeRestrict_surjective
  have hk:f.ker=C.subgroupOf K := by
    change (eK.toMonoidHom.comp φ.rangeRestrict).ker=C.subgroupOf K
    rw [MonoidHom.ker_comp_of_injective _ _ eK.injective,MonoidHom.ker_rangeRestrict]
    ext x
    change inclusion hKA x∈A.normalizerMonoidHom.ker ↔ (x:G)∈C
    rw [normalizerMonoidHom_ker]
    rfl
  have hkp:IsPGroup 2 f.ker := hk.symm ▸ hCp.comap_subtype
  let : (A.subgroupOf K).Normal := (normal_subgroupOf_iff_le_normalizer hAK).mpr hKA
  have hAker:A.subgroupOf K≤f.ker := by
    rw [hk]
    exact fun _ hx=>A.le_centralizer hx
  have hRne:(R.subgroupOf K).map f≠⊥ := by
    intro he
    have hle:R≤A := by
      intro r hrR
      have hx:((⟨r,hRK hrR⟩:K):G)∈C := by
        change (⟨r,hRK hrR⟩:K)∈C.subgroupOf K
        rw [←hk]
        exact (map_eq_bot_iff (R.subgroupOf K)).mp he hrR
      exact hRC.le ⟨hrR,hx⟩
    have hh:=card_le_of_le hle
    rw [hRc,hAc] at hh
    omega
  have heker:f.ker=A.subgroupOf K :=
    AlternatingSix.kernel_eq_of_square_normal_generator f hf hkp hKp
      (A.subgroupOf K) (R.subgroupOf K) hAker hRne
      (commutator_le.mpr (by
        intro c hc r hrR
        exact hcomm (commutator_mem_commutator (show (c:G)∈C from (show c∈C.subgroupOf K from hk ▸ hc)) hrR)))
      (fun r hrR=>hsq r hrR)
  have hKC:K⊓C=A := by
    have he:=congrArg (Subgroup.map K.subtype) (hk.symm.trans heker)
    simpa only [subgroupOf_map_subtype,map_subgroupOf_eq_of_le hAK,inf_comm C K] using he
  have hkcard:Nat.card f.ker=16 := by
    rw [heker,Nat.card_congr (subgroupOfEquivOfLe hAK).toEquiv,hAc]
  have hKcard:Nat.card K=5760 := by
    have hh:=f.ker.index_mul_card
    rw [index_ker,MonoidHom.range_eq_top.mpr hf,card_top,hkcard,nat_card_alternatingGroup] at hh
    norm_num [Nat.factorial] at hh
    omega
  refine ⟨hKC,hKcard,?_⟩
  let S:=R⊔F.U
  have hSc:Nat.card S=128 := factor_join_order_of_full_orthogonal
    hG T hempty hM hu hmany hcard e hnot F dg hZ hne g hgP hgH hr
  have hSkc:Nat.card (S.subgroupOf K)=128 :=
    (Nat.card_congr (subgroupOfEquivOfLe hSK).toEquiv).trans hSc
  have hp:IsPGroup 2 (S.subgroupOf K) := IsPGroup.of_card (n:=7) (by norm_num;exact hSkc)
  have hi:(S.subgroupOf K).index=45 := by
    have hh:=(S.subgroupOf K).index_mul_card
    rw [hSkc,hKcard] at hh
    omega
  refine ⟨hp.toSylow (by rw [hi];decide),?_⟩
  exact map_subgroupOf_eq_of_le hSK
theorem factor_block_core_of_full_orthogonal
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
    (hVA:rankTwoSeed T M≤A) (hAc:Nat.card A=16)
    (hc8:Nat.card (A⊓F.U:Subgroup G)=8)
    (hAB:A⊔B=(F.I₂ (sourceResidual M Mc)).pCoreIn 2)
    (hRc:Nat.card ((F.I₂ (sourceResidual M Mc)).pCoreIn 2)=64)
    (hAN:F.I₂ (sourceResidual M Mc)⊔F.H.pCoreIn 2≤normalizer (A:Set G)) :
    let R := (F.I₂ (sourceResidual M Mc)).pCoreIn 2
    let N := F.H⊓normalizer (A:Set G)
    let Y := (pResidual 2 N).map N.subtype
    let K := sourceResidual M Mc⊔Y
    K.pCoreIn 2=A ∧ K⊓centralizer (A:Set G)=A ∧
      ⁅K,centralizer (A:Set G)⁆≤A ∧ Nat.card K=5760 ∧
      ∃P:Sylow 2 K,(P:Subgroup K).map K.subtype=R⊔F.U := by
  intro R N Y K
  obtain ⟨hKA,⟨eK⟩⟩ := factor_alternating_automizer_of_full_orthogonal
    hG T hempty hM hu hmany hcard e hnot F dg hZ hne g hgP hgH hr
    A B hAR hBR hVA hAc hc8 hAB hRc hAN
  obtain ⟨hKC,hKcard,hP⟩ := factor_block_kernel_of_action
    hG T hempty hM hu hmany hcard e hnot F dg hZ hne g hgP hgH hr
    A B hAR hBR hVA hAc hc8 hAB hRc hAN hKA eK
  have hpc := (factor_core_quotient_of_full_orthogonal
    hG T hempty hM hu hmany hcard e hnot F dg hZ hne g hgP hgH hr
    A B hAR hBR hVA hAc hc8 hAB hRc hAN).1
  have hCK := (factor_generated_residual_geometry_of_full_orthogonal
    hG T hempty hM hu hmany hcard e hnot F dg hZ hne g hgP hgH hr
    A hAR hVA hAc hc8 hAN).2.2.2
  have hcomm:⁅K,centralizer (A:Set G)⁆≤A :=
    (le_inf (le_normalizer_iff_commutator_le_left.mp hCK)
      (le_normalizer_iff_commutator_le_right.mp
        (hKA.trans (normalizer_le_normalizer_centralizer A)))).trans hKC.le
  exact ⟨hpc.trans hKC,hKC,hcomm,hKcard,hP⟩

theorem source_factor_block_core_of_solvable
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (hnot : ¬ ClassificationModels.IsTheoremEModel G)
    (F : InvariantFlag T (rankTwoSeed T M) 2)
    [IsElementaryAbelian 2 (rankTwoSeed T M)]
    (hne : ¬ IsMulCommutative F.U)
    (g : G) (hgP : g∈F.P (sourceResidual M Mc)) (hgH : g∉F.H)
    (hs : Group.IsSolvable F.TerminalHdot)
    (A:Subgroup G) [IsElementaryAbelian 2 A]
    (hAR:A≤(F.I₂ (sourceResidual M Mc)).pCoreIn 2)
    (hVA:rankTwoSeed T M≤A) (hAc:Nat.card A=16)
    (hc8:Nat.card (A⊓F.U:Subgroup G)=8)
    (hAN:F.I₂ (sourceResidual M Mc)⊔F.H.pCoreIn 2≤normalizer (A:Set G)) :
    let R := (F.I₂ (sourceResidual M Mc)).pCoreIn 2
    let N := F.H⊓normalizer (A:Set G)
    let Y := (pResidual 2 N).map N.subtype
    let K := sourceResidual M Mc⊔Y
    K.pCoreIn 2=A ∧ K⊓centralizer (A:Set G)=A ∧
      ⁅K,centralizer (A:Set G)⁆≤A ∧ Nat.card K=5760 ∧
      ∃P:Sylow 2 K,(P:Subgroup K).map K.subtype=R⊔F.U := by
  let h:=source_lemma_14_2_4 hG T hempty hM hu hmany hcard e
  obtain ⟨dg,he,_,_,_,_,_⟩:=rankTwo_terminal_hypothesis h F hne g hgP hgH
  let := he
  have hZ:=source_center_eq_point_of_solvable hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs
  have hr:=source_full_orthogonal_of_solvable hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs
  obtain ⟨C,D,hCR,hDR,hVC,hVD,hEC,hED,hCc,hDc,hCDi,hCD,hRc,hCN,hDN,hmax⟩ :=
    maximal_elementary_factors_of_full_orthogonal hG T hempty hM hu hmany hcard e hnot
      F dg hZ hne g hgP hgH hr
  let := hEC
  let := hED
  rcases hmax A inferInstance hAR with hac|had
  · have heq:A=C := eq_of_le_of_card_ge hac (by rw [hAc,hCc])
    exact factor_block_core_of_full_orthogonal
      hG T hempty hM hu hmany hcard e hnot F dg hZ hne g hgP hgH hr
      A D hAR hDR hVA hAc hc8 (by simpa [heq] using hCD) hRc hAN
  · have heq:A=D := eq_of_le_of_card_ge had (by rw [hAc,hDc])
    exact factor_block_core_of_full_orthogonal
      hG T hempty hM hu hmany hcard e hnot F dg hZ hne g hgP hgH hr
      A C hAR hCR hVA hAc hc8 (by simpa [heq,sup_comm] using hCD) hRc hAN

end CFSG.Quasithin.Chapter14.Section03.NonabelianSource.Recognition
