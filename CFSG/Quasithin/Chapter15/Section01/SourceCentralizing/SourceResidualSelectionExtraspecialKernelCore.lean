module

public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionExtraspecialKernelSylow
public import Theory.GroupTheory.PCoreImage

/-!
# The original moved-plane centralizer has the partner's two-core

The actual partner module is U=[V,J₁(T)]. Reducedness makes O₂(Mc)
centralize U. Since C_G(U) is normal in Mc=N_G(U), relative core
monotonicity identifies its two-core with O₂(Mc). In particular that core
lies in the original Sylow subgroup and normalizes the original fixed
subgroup. The entire centralizer's action on that fixed subgroup remains a
separate duty.
-/

public section
open Subgroup Stellmacher Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section01
open Section03 Section03.InitialSource ChapterA.Section05To06 ChapterD ChapterD.UniqueFactor
variable {G : Type*} [Group G] [Finite G]

/-- The centralizer kernel and its literal partner have the same embedded
two-core; it lies in T and normalizes the original Thompson fixed subgroup. -/
theorem PreparedChosenModule.extraspecial_moved_centralizer_twoCore
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc V : Subgroup G} (hM : IsOrderingMaximal T M)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (h : PreparedChosenModule T M V) (hfull : V = localModule T M)
    (hex : letI := h.elementary; SourceCases.Extraspecial (imageRepresentation M V h.normalized)
      (((T : Subgroup G).subgroupOf M).map (actionHom M V h.normalized).rangeRestrict)) :
    let U := ⁅V,ChapterB.thompsonJ (T : Subgroup G) 1⁆
    let C := centralizer (U : Set G)
    C.pCoreIn 2 = Mc.pCoreIn 2 ∧ C.pCoreIn 2 ≤ (T : Subgroup G) ∧
      C.pCoreIn 2 ≤ normalizer (thompsonFixed T V : Set G) ∧
      C ⊓ centralizer (C.pCoreIn 2 : Set G) ≤ C.pCoreIn 2 := by
  let U := ⁅V,ChapterB.thompsonJ (T : Subgroup G) 1⁆
  let C := centralizer (U : Set G)
  have hmod := h.extraspecial_partner_module_and_normalizer
    hG T hempty hM hmany hJ hu hfull hex
  have hMcC : Mc ∈ maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) :=
    hu ▸ Set.mem_singleton Mc
  have hTMc : (T : Subgroup G) ≤ Mc := by
    intro t ht
    exact hMcC.2 (fun z hz => (centralInvolutions_le_centralizer_sylow T hz t ht).symm)
  have hMcH : Mc ∈ Chapter1.HOver G (T : Set G) :=
    ⟨Chapter1.mem_H_of_isTwoLocal hMcC.1.1,hTMc⟩
  have hCN : Mc ≤ normalizer (C : Set G) := by
    rw [hmod.2]
    exact normalizer_le_normalizer_centralizer _
  have hCMc : C ≤ Mc := by
    rw [hmod.2]
    exact Subgroup.centralizer_le_normalizer _
  have hQC : Mc.pCoreIn 2 ≤ C := by
    have hred := localModule_reduced_from_source hG T hMcH
    rintro x ⟨q,hq,rfl⟩ u hu
    have huL : u ∈ localModule T Mc := hmod.1.symm ▸ hu
    exact congrArg Mc.subtype ((le_centralizer_iff.mp hred.le_centralizer_pCore)
      hq ⟨u,localModule_le T hTMc huL⟩ huL)
  have he : C.pCoreIn 2 = Mc.pCoreIn 2 := le_antisymm
    (pCoreIn_mono_of_normalizes hCMc hCN)
    (le_pCoreIn_of_normalizes (isPGroup_pCoreIn 2 Mc) hQC
      (hCMc.trans (Mc.le_normalizer.trans
        (normalizer_le_normalizer_characteristic_image Mc (pCore 2 Mc)))))
  have hCT : C.pCoreIn 2 ≤ (T : Subgroup G) := by
    rw [he]
    have hh := pCoreIn_le_sylow Mc (T.subtype hTMc)
    rwa [Sylow.coe_subtype,map_subgroupOf_eq_of_le hTMc] at hh
  have hTE : (T : Subgroup G) ≤ normalizer (thompsonFixed T V : Set G) :=
    (le_inf (hM.1.2.trans h.normalized)
      ((ChapterB.le_normalizer_thompsonJ _ _).trans
        (normalizer_le_normalizer_centralizer _))).trans inf_normalizer_le_normalizer_inf
  refine ⟨he,hCT,hCT.trans hTE,?_⟩
  rw [he]
  exact (inf_le_inf_right _ hCMc).trans
    (Chapter1.lemma_1_1_4_6 T (hG.evenCharacteristic T) hMcH)

end CFSG.Quasithin.Chapter15.Section01
