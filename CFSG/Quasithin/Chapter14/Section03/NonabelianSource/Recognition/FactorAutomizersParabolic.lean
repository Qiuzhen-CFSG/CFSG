module
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.Recognition.FactorAutomizers
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.Recognition.ParabolicResidual
public import Theory.GroupTheory.ResidualGeneratedFourSymmetricFour
public import Theory.GroupTheory.PCoreSurjective
public import Theory.GroupTheory.PResidual.FiniteImage

public import Theory.GroupTheory.ElementaryEightFixedPointDihedral

/-! The original parabolic I₂ induces S₄ on either chosen elementary factor.
The kernel is A, so the image has order 24 and elementary two-core of order 4.
The source equality R=[R,O²(I₂)] makes that four self-centralizing.
All homomorphisms are the literal normalizer conjugation maps.
Source: Aschbacher–Smith 14.3.19. -/

@[expose] public noncomputable section
open Subgroup Module Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section03.NonabelianSource.Recognition
open Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter12.Section08.InvariantFlag.Symplectic
open Chapter14.Section02 SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
variable {G:Type*} [Group G] [Finite G]

theorem factor_parabolic_symmetric_automizer_of_full_orthogonal
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
    (hIA:F.I₂ (sourceResidual M Mc)≤normalizer (A:Set G)) :
    Nat.card (A.normalizerMonoidHom.comp (inclusion hIA)).range=24 ∧
    Nonempty ((A.normalizerMonoidHom.comp (inclusion hIA)).range ≃* Equiv.Perm (Fin 4)) := by
  let h := source_lemma_14_2_4 hG T hempty hM hu hmany hcard e
  let L := sourceResidual M Mc
  let : Fact (IsPGroup 2 F.U) := ⟨dg.two⟩
  have hPhi : (frattini F.U).map F.U.subtype=F.Vi 1 := by
    rw [dg.frattini_point]
    exact map_subgroupOf_eq_of_le ((F.le_seed 1).trans (le_conjugateSpanBy _ _))
  have hcomm : ⁅F.U,F.U⁆≤F.Vi 1 := by
    rw [←F.U.map_subtype_commutator]
    exact (map_mono (f:=F.U.subtype) (commutator_le_frattini_of_isPGroup (p:=2))).trans hPhi.le
  have hsquare : ∀u∈F.U,u^2∈F.Vi 1 := fun u hu=>
    hPhi ▸ mem_map_of_mem F.U.subtype (pth_power_mem_frattini_of_isPGroup (p:=2) (⟨u,hu⟩:F.U))
  have hspan : F.U=conjugateSpanBy (F.Vi 2) F.H := by rw [F.last]; rfl
  obtain ⟨e₀,_,hgen,_,hIG,_,_,_,hfactor,hPH,hcore,hindex,_⟩ :=
    F.binary_generation (by decide) L h.L_normalizes_seed (h.binarySeedAction_surjective F)
      h.centralizer hcomm hsquare hspan hne g hgP hgH
  let I:=F.I₂ L
  let R:=I.pCoreIn 2
  have hAI:A≤I := hAR.trans (pCoreIn_le 2 I)
  have hBI:B≤I := hBR.trans (pCoreIn_le 2 I)
  have hcentJ:((R⊔F.U)⊓centralizer ((A⊓F.U:Subgroup G):Set G):Subgroup G)=A :=
    elementary_factor_join_centralizer_of_full_orthogonal
      hG T hempty hM hu hmany hcard e hnot F dg hZ hne g hgP hgH hr A hAR hVA hAc hc8
  have hcentI:I⊓centralizer (A:Set G)=A := by
    apply le_antisymm
    · rintro x ⟨hxI,hxC⟩
      have hxR:x∈R := by
        apply hcore.le
        refine ⟨hxI,?_⟩
        rw [F.last]
        exact centralizer_le hVA hxC
      apply hcentJ.le
      exact ⟨(show R≤R⊔F.U from le_sup_left) hxR,centralizer_le (show (A⊓F.U:Subgroup G)≤A from inf_le_left) hxC⟩
    · exact le_inf hAI A.le_centralizer
  let φ:=A.normalizerMonoidHom.comp (inclusion hIA)
  let X:=φ.range
  let f:I→*X:=φ.rangeRestrict
  have hf:Function.Surjective f:=φ.rangeRestrict_surjective
  have hk:f.ker=A.subgroupOf I := by
    rw [MonoidHom.ker_rangeRestrict]
    ext x
    change inclusion hIA x∈A.normalizerMonoidHom.ker ↔ (x:G)∈A
    rw [normalizerMonoidHom_ker]
    change (x:G)∈centralizer (A:Set G) ↔ (x:G)∈A
    conv_rhs => rw [←hcentI]
    have hxI:(x:G)∈I:=x.property
    simp only [mem_inf,hxI,true_and]
  have hkc:Nat.card f.ker=16 := by
    rw [hk,Nat.card_congr (subgroupOfEquivOfLe hAI).toEquiv,hAc]
  let : IsElementaryAbelian 2 (A.subgroupOf I) := IsElementaryAbelian.subgroupOf hAI
  have hkp:IsPGroup 2 f.ker := hk ▸ IsElementaryAbelian.isPGroup 2 (A.subgroupOf I)
  have hpc:Nat.card (pCore 2 I)=64 := by
    rw [←hRc]
    exact (card_map_of_injective (K:=pCore 2 I) I.subtype_injective).symm
  have hquot:Nat.card (I⧸pCore 2 I)=6 := by
    rw [Nat.card_congr e₀.toEquiv]
    norm_num [Nat.card_eq_fintype_card,Fintype.card_perm,Nat.factorial]
  have hIc:Nat.card I=384 := by
    have hh:=(pCore 2 I).card_eq_card_quotient_mul_card_subgroup
    rw [hpc,hquot] at hh
    exact hh
  have hXc:Nat.card X=24 := by
    have hh:=f.ker.index_mul_card
    rw [index_ker,MonoidHom.range_eq_top.mpr hf,card_top,hkc,hIc] at hh
    omega
  have hU:(pCore 2 I).map f=pCore 2 X := by
    rw [←f.comap_pCore_of_ker_isPGroup hf hkp,map_comap_eq_self_of_surjective hf]
  have hUc:Nat.card (pCore 2 X)=4 := by
    have hh:=f.card_pCore_of_ker_isPGroup hf hkp
    rw [hpc,hkc] at hh
    omega
  have hRsub:R.subgroupOf I=pCore 2 I := by
    apply Subgroup.map_injective I.subtype_injective
    rw [map_subgroupOf_eq_of_le (pCoreIn_le 2 I)]
    rfl
  have hA0:(A.subgroupOf I).map f=⊥ :=
    (Subgroup.map_eq_bot_iff _).mpr hk.ge
  have hUB:pCore 2 X=(B.subgroupOf I).map f := by
    rw [←hU,←hRsub,show R=A⊔B from hAB.symm,subgroupOf_sup hAI hBI,Subgroup.map_sup,hA0,bot_sup_eq]
  let : IsElementaryAbelian 2 (B.subgroupOf I) := IsElementaryAbelian.subgroupOf hBI
  have hUE:IsElementaryAbelian 2 (pCore 2 X) := hUB ▸ IsElementaryAbelian.map f
  let := hUE
  obtain ⟨hL,hRL,_,_⟩ := parabolic_residual_core_structure_of_full_orthogonal
    hG T hempty hM hu hmany hcard e hnot F dg hZ hne g hgP hgH hr
  have hRI:⁅pCore 2 I,pResidual 2 I⁆=pCore 2 I := by
    apply Subgroup.map_injective I.subtype_injective
    rw [map_commutator,hL]
    exact hRL.symm
  have hRX:⁅pCore 2 X,pResidual 2 X⁆=pCore 2 X := by
    have hh:=congrArg (fun K:Subgroup I=>K.map f) hRI
    rw [map_commutator,hU,map_pResidual_of_surjective 2 f hf] at hh
    exact hh
  exact ⟨hXc,symmetricFour_of_residual_generated_four (pCore 2 X) hUc hXc le_rfl hRX⟩
end CFSG.Quasithin.Chapter14.Section03.NonabelianSource.Recognition
