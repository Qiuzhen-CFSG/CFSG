module

public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionExtraspecialKernelFixedEnvelope
public import Theory.GroupTheory.ThreeStepChainCentralizerTwoCore

/-!
# The full original module lies in the moved-plane centralizer's two-core

The centralizer span F of E is normal in C=C_G(U). The original module V
centralizes U and acts trivially on F/U and Q/F, where Q=O₂(C). The
three-step chain theorem therefore places V in Q under the original source
hypotheses, without a choice between the two intersection alternatives.
-/

public section
open Subgroup Stellmacher Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section01
open Section03 Section03.InitialSource ChapterA.Section05To06 ChapterD ChapterD.UniqueFactor
variable {G : Type*} [Group G] [Finite G]

/-- The original six-dimensional module lies in O₂(C_G(U)), because it
centralizes each factor of the original normal chain Q > F > U > 1. -/
theorem PreparedChosenModule.extraspecial_module_le_moved_centralizer_twoCore
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
    V ≤ (centralizer (U : Set G)).pCoreIn 2 := by
  let := h.elementary
  let U := ⁅V,ChapterB.thompsonJ (T : Subgroup G) 1⁆
  let E := thompsonFixed T V
  let C := centralizer (U : Set G)
  let Q := C.pCoreIn 2
  let F := conjugateSpanBy E C
  have hUV : U ≤ V := (h.extraspecial_thompson_moved_le_fixed
    hG T hempty hM hmany hJ hfull hex).trans inf_le_left
  have hVC : V ≤ C := V.le_centralizer.trans (centralizer_le hUV)
  have hUC : U ≤ C := hUV.trans hVC
  have hCQ : C ≤ normalizer (Q : Set G) := C.le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image C (pCore 2 C))
  have hspan := h.extraspecial_kernel_span_structure
    hG T hempty hM hmany hJ hu hfull hex
  have hFC : F ≤ C := hspan.1.trans (pCoreIn_le 2 C)
  have hCF : C ≤ normalizer (F : Set G) := hspan.2.2.1
  have hself : C ⊓ centralizer (Q : Set G) ≤ Q :=
    (h.extraspecial_moved_centralizer_twoCore hG T hempty hM hmany hJ hu hfull hex).2.2.2
  have hVF : ⁅V,F⁆ ≤ U := h.extraspecial_kernel_span_full_displacement
    hG T hempty hM hmany hJ hu hfull hex
  have hVQ : ⁅V,Q⁆ ≤ F := by
    rw [commutator_comm]
    exact (h.extraspecial_moved_centralizer_full_displacement
      hG T hempty hM hmany hJ hu hfull hex).trans (le_conjugateSpanBy E C)
  exact le_twoCore_of_relative_three_step_chain C Q F U V
    (pCoreIn_le 2 C) hFC hUC hVC hCQ hCF (Subgroup.centralizer_le_normalizer _)
    (isPGroup_pCoreIn 2 C) hself hVC hVF hVQ

end CFSG.Quasithin.Chapter15.Section01
