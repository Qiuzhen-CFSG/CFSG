module

public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionExtraspecialKernelContainedCore
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionExtraspecialKernelImage

/-!
# The two remaining original extraspecial kernel configurations

The original full source either has an elementary full-module span in
both local two-cores, or has exact intersection sixteen and an order-four
actor in the actual core image with saturated displacement layers.
Neither branch assumes the global residual theorem. The quartic actor is
in the action image; no order-four lift to the ambient core is asserted.
-/

public section
open Subgroup Stellmacher Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section01
open Section03 Section03.InitialSource ChapterA.Section05To06 ChapterD ChapterD.UniqueFactor
variable {G : Type*} [Group G] [Finite G]

/-- A source consequence retaining both genuine kernel configurations
under the original full extraspecial hypotheses. -/
theorem PreparedChosenModule.extraspecial_kernel_source_alternatives
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
    let E := thompsonFixed T V
    let C := centralizer (U : Set G)
    let Q := C.pCoreIn 2
    let H := conjugateSpanBy V C
    let F := conjugateSpanBy E C
    let f := (actionHom M V h.normalized).rangeRestrict
    let B := (Q.subgroupOf M).map f
    let R := ((ChapterB.thompsonJ (T : Subgroup G) 1).subgroupOf M).map f
    (V ≤ Q ∧ IsElementaryAbelian 2 H ∧ H ≤ Q ⊓ M.pCoreIn 2 ∧
      Mc ≤ normalizer (H : Set G) ∧ H ≤ centralizer (V : Set G) ∧ F ≤ H ∧ ⁅Q,H⁆ ≤ F) ∨
    (V ⊓ Q = E ∧ ∃ t, orderOf t = 2 ∧ zpowers t = R ∧
      ∃ x ∈ B, orderOf x = 4 ∧ x ^ 2 = t ∧ ⁅Q,V⁆ = E ∧ ⁅Q,E⁆ = U) := by
  rcases h.extraspecial_module_intersection_core hG T hempty hM hmany hJ hu hfull hex with he | hc
  · exact Or.inr ⟨he,h.extraspecial_exact_intersection_core_image
      hG T hempty hM hmany hJ hu hfull hex he⟩
  · have hs := h.extraspecial_contained_module_span
      hG T hempty hM hmany hJ hu hfull hex hc
    have hk := h.extraspecial_contained_span_le_selected_core
      hG T hempty hM hmany hJ hu hfull hex hc
    exact Or.inl ⟨hc,hs.1,le_inf hs.2.1 hk.1,hs.2.2.1,hk.2,hs.2.2.2⟩

end CFSG.Quasithin.Chapter15.Section01
