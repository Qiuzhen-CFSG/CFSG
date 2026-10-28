module
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.Recognition.FactorAutomizersGeometry

/-! The original elementary factor has a two-group centralizer in H.
Its terminal centralizer image lies in the factor's own involution image,
and the terminal kernel is O₂(H). Source: Aschbacher–Smith 14.3.19. -/

@[expose] public noncomputable section
open Subgroup Module Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section03.NonabelianSource.Recognition
open Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter12.Section08.InvariantFlag.Symplectic
open Chapter14.Section02 SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
variable {G:Type*} [Group G] [Finite G]

theorem elementary_factor_centralizer_twoGroup_of_full_orthogonal
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
    F.terminalDot (F.H⊓centralizer (A:Set G))≤F.terminalDot A ∧
    IsPGroup 2 (F.H⊓centralizer (A:Set G):Subgroup G) := by
  let R:=(F.I₂ (sourceResidual M Mc)).pCoreIn 2
  let q:=QuotientGroup.mk' F.terminalHatAction.ker
  have hRT:R≤(T:Subgroup G) := (parabolic_core_sylow_index_of_full_orthogonal
    hG T hempty hM hu hmany hcard e hnot F dg hZ hne g hgP hgH hr).1
  have hAH:A≤F.H := hAR.trans (hRT.trans (F.invariant 1))
  have hnotAU:¬A≤F.U := by
    intro hh
    rw [inf_eq_left.mpr hh,hAc] at hc8
    contradiction
  obtain ⟨a,ha,haU⟩:=SetLike.not_le_iff_exists.mp hnotAU
  let C := F.H⊓centralizer (A:Set G)
  have hdot:F.terminalDot C≤F.terminalDot A := by
    rintro t ⟨b,hb,rfl⟩
    rcases elementary_factor_pointwise_terminal_stabilizer
      hG T hempty hM hu hmany hcard e hnot F dg hZ hne g hgP hgH hr
      A hAR hAH hVA hc8 a ha haU b (fun u hu=>(hb.2 (u:G) hu).symm) with hb1 | hba
    · rw [hb1]
      exact one_mem _
    · rw [hba]
      exact mem_map_of_mem q (show (⟨a,hAH ha⟩:F.H)∈A.subgroupOf F.H from ha)
  refine ⟨hdot,?_⟩
  have hAdot:IsPGroup 2 (F.terminalDot A) :=
    ((IsElementaryAbelian.isPGroup 2 A).comap_of_injective F.H.subtype
      F.H.subtype_injective).map q
  have hker:IsPGroup 2 q.ker := by
    change IsPGroup 2 (QuotientGroup.mk' F.terminalHatAction.ker).ker
    rw [QuotientGroup.ker_mk',terminal_kernel_of_center_point F dg hZ]
    exact pCore_isPGroup
  have hCH:IsPGroup 2 (C.subgroupOf F.H) :=
    ((hAdot.to_le hdot).comap_of_ker_isPGroup q hker).to_le (le_comap_map _ _)
  exact hCH.of_surjective
    (subgroupOfEquivOfLe (show C≤F.H from inf_le_left)).toMonoidHom
    (subgroupOfEquivOfLe (show C≤F.H from inf_le_left)).surjective
end CFSG.Quasithin.Chapter14.Section03.NonabelianSource.Recognition
