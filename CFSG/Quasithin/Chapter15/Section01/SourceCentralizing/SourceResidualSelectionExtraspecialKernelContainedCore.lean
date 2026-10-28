module

public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionExtraspecialKernelContained

/-!
# The elementary full-module span lies in both original two-cores

In the contained branch the actual C_G(U)-span H of V is elementary and
Mc-normalized. It centralizes V and lies in M, hence in K=C_M(V). Since
K≤Mc, K normalizes H. Thus H≤O₂(K)≤O₂(M), using the actual normality of
K in M. No normality of H under all of M is inferred.
-/

public section
open Subgroup Stellmacher Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section01
open Section03 Section03.InitialSource ChapterA.Section05To06 ChapterD ChapterD.UniqueFactor
variable {G : Type*} [Group G] [Finite G]

/-- The same elementary centralizer span lies in the selected core and
centralizes the original full module. -/
theorem PreparedChosenModule.extraspecial_contained_span_le_selected_core
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc V : Subgroup G} (hM : IsOrderingMaximal T M)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (h : PreparedChosenModule T M V) (hfull : V = localModule T M)
    (hex : letI := h.elementary; SourceCases.Extraspecial (imageRepresentation M V h.normalized)
      (((T : Subgroup G).subgroupOf M).map (actionHom M V h.normalized).rangeRestrict))
    (hVQ : V ≤ (centralizer
      ((⁅V,ChapterB.thompsonJ (T : Subgroup G) 1⁆ : Subgroup G) : Set G)).pCoreIn 2) :
    let U := ⁅V,ChapterB.thompsonJ (T : Subgroup G) 1⁆
    let H := conjugateSpanBy V (centralizer (U : Set G))
    H ≤ M.pCoreIn 2 ∧ H ≤ centralizer (V : Set G) := by
  let U := ⁅V,ChapterB.thompsonJ (T : Subgroup G) 1⁆
  let C := centralizer (U : Set G)
  let H := conjugateSpanBy V C
  let K := M ⊓ centralizer (V : Set G)
  have hs := h.extraspecial_contained_module_span
    hG T hempty hM hmany hJ hu hfull hex hVQ
  let : IsElementaryAbelian 2 H := hs.1
  have hHV : H ≤ centralizer (V : Set G) :=
    H.le_centralizer.trans (centralizer_le (le_conjugateSpanBy V C))
  have hcore := h.extraspecial_moved_centralizer_twoCore
    hG T hempty hM hmany hJ hu hfull hex
  have hHK : H ≤ K := le_inf (hs.2.1.trans (hcore.2.1.trans hM.1.2)) hHV
  have hKMc : K ≤ Mc := inf_le_right.trans (h.centralizer_le_partner T hu)
  have hKH : K ≤ normalizer (H : Set G) := hKMc.trans hs.2.2.1
  have hHcore : H ≤ K.pCoreIn 2 :=
    le_pCoreIn_of_normalizes (IsElementaryAbelian.isPGroup 2 H) hHK hKH
  have hMK : M ≤ normalizer (K : Set G) :=
    (le_inf M.le_normalizer (h.normalized.trans
      (normalizer_le_normalizer_centralizer _))).trans inf_normalizer_le_normalizer_inf
  exact ⟨hHcore.trans (pCoreIn_mono_of_normalizes inf_le_left hMK),hHV⟩

end CFSG.Quasithin.Chapter15.Section01
