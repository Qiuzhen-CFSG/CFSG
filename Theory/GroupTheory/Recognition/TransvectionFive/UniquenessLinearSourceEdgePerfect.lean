module
public import Theory.GroupTheory.Recognition.TransvectionFive.UniquenessLinearSourceEdgeStructure
public import Theory.SpecificGroups.BinaryLinear.Perfect
public import Theory.GroupTheory.Commutator.PerfectQuotient
import all Theory.GroupTheory.Recognition.TransvectionFive.UniquenessLinearSourceTensorProduct
import all Theory.GroupTheory.Recognition.TransvectionFive.UniquenessMathieu.OctadGraph.Source.LinePlane

public noncomputable section
open Subgroup
open scoped commutatorElement
namespace Theory.GroupTheory.TransvectionFive.UniquenessLinear.SourceGeometry
open PlaneTensor PlaneCensus GraphUniquenessSystem GraphUniquenessSystem.Cosets
open UniquenessMathieu.OctadSource (tensor_decomposition)
variable {G : Type*} [Group G] [Finite G] {z : G}
  (F : MarkedCentralizer z) (hlinear : F.LinearFusion)

private theorem tensor_add (i : Fin 3) (v w : Fin 3 → ZMod 2) :
    tensorCode i (v + w) = tensorCode i v ^^^ tensorCode i w := by decide +revert

private theorem tensor_zero (i : Fin 3) : tensorCode i 0 = 0 := by decide +revert

private theorem tensor_mem_commutator (i : Fin 3) (v : Fin 3 → ZMod 2) :
    (⟨element F (tensorCode i v), rectangle_le_edgeGroup F hlinear (element_mem F _)⟩ :
      edgeGroup F hlinear) ∈ commutator (edgeGroup F hlinear) := by
  by_cases hv : v = 0
  · subst v
    have he : (⟨element F (tensorCode i 0), rectangle_le_edgeGroup F hlinear (element_mem F _)⟩ :
        edgeGroup F hlinear) = 1 := by
      apply Subtype.ext
      exact (congrArg (element F) (tensor_zero i)).trans (element_zero F)
    rw [he]
    exact (commutator (edgeGroup F hlinear)).one_mem
  obtain ⟨w, hw, hwv⟩ := (by decide : ∀ v : Fin 3 → ZMod 2,
    ∃ w, w ≠ 0 ∧ w ≠ v) v
  have hsum : v + w ≠ 0 := by
    intro he
    have he' : ∀ v w : Fin 3 → ZMod 2, v + w = 0 → w = v := by decide
    exact hwv (he' v w he)
  have hsumv : v + w ≠ v := by
    intro he
    exact hw (add_left_cancel (he.trans (add_zero v).symm))
  obtain ⟨f, hfw, _⟩ := BinaryLinear.exists_linearEquiv_pair w v (v + w) v
    hw hv hsum hv hwv hsumv
  obtain ⟨n, hn⟩ := edgeLinearAction_surjective F hlinear f
  let a : edgeGroup F hlinear :=
    ⟨element F (tensorCode i w), rectangle_le_edgeGroup F hlinear (element_mem F _)⟩
  have he : ⁅n, a⁆ = (⟨element F (tensorCode i v),
      rectangle_le_edgeGroup F hlinear (element_mem F _)⟩ : edgeGroup F hlinear) := by
    apply Subtype.ext
    change (n : G) * element F (tensorCode i w) * (n : G)⁻¹ *
      (element F (tensorCode i w))⁻¹ = element F (tensorCode i v)
    rw [← edgeLinearAction_tensor F hlinear n i w, hn, hfw, tensor_add, element_xor]
    exact mul_inv_cancel_right _ _
  rw [← he]
  exact commutator_mem_commutator (mem_top _) (mem_top _)

theorem rectangle_le_edge_commutator :
    F.plane.subgroupOf (edgeGroup F hlinear) ≤ commutator (edgeGroup F hlinear) := by
  intro a ha
  obtain ⟨x, hx⟩ := (sourceEquiv F).surjective ⟨a, ha⟩
  have hxa : element F x = (a : G) := congrArg Subtype.val hx
  obtain ⟨v, w, hvw, _⟩ := tensor_decomposition x
  have hm := (commutator (edgeGroup F hlinear)).mul_mem
    (tensor_mem_commutator F hlinear 0 v) (tensor_mem_commutator F hlinear 1 w)
  have he : (⟨element F (tensorCode 0 v), rectangle_le_edgeGroup F hlinear (element_mem F _)⟩ :
      edgeGroup F hlinear) *
    ⟨element F (tensorCode 1 w), rectangle_le_edgeGroup F hlinear (element_mem F _)⟩ = a := by
    apply Subtype.ext
    change element F (tensorCode 0 v) * element F (tensorCode 1 w) = (a : G)
    rw [← element_xor, hvw, hxa]
  exact he ▸ hm

theorem edgeGroup_isPerfect : Group.IsPerfect (edgeGroup F hlinear) := by
  let := BinaryLinear.linearGroup_isPerfect 3 (by decide)
  constructor
  have h := CentralExtension.ker_sup_commutator_eq_top_of_surjective
    (edgeLinearAction F hlinear) (edgeLinearAction_surjective F hlinear)
  rw [edgeLinearAction_kernel,
    sup_eq_right.mpr (rectangle_le_edge_commutator F hlinear)] at h
  exact h

/-- The actual source edge fixer lies in its point–line flag stabilizer. -/
theorem edgeGroup_le_pointLine :
    edgeGroup F hlinear ≤ rowNormalizer F ⊓ sourcePlaneNormalizer F := by
  intro b hb
  refine ⟨?_, edgeFixer_le_line F hlinear hb⟩
  have hx := hb.1
  change b ∈ MulAction.stabilizer G (vertex (rowNormalizer F) 1) at hx
  change b ∈ rowNormalizer F
  simpa only [stabilizer_base] using hx

/-- The edge fixer is intrinsic to the point–line stabilizer: its derived subgroup. -/
theorem pointLine_commutator :
    ⁅rowNormalizer F ⊓ sourcePlaneNormalizer F,
      rowNormalizer F ⊓ sourcePlaneNormalizer F⁆ = edgeGroup F hlinear := by
  apply le_antisymm
  · apply commutator_le.mpr
    rintro a ⟨haM, haP⟩ b ⟨hbM, hbP⟩
    let a' : sourcePlaneNormalizer F := ⟨a, haP⟩
    let b' : sourcePlaneNormalizer F := ⟨b, hbP⟩
    apply (line_edgeFixer_iff F hlinear ⁅a', b'⁆).mpr
    rw [map_commutatorElement]
    apply commutatorElement_eq_one_iff_mul_comm.mpr
    exact (by decide : ∀ p q : Equiv.Perm (Fin 3), p 0 = 0 → q 0 = 0 → p * q = q * p)
      _ _ ((lineAction_fix_iff F hlinear a').mpr haM)
      ((lineAction_fix_iff F hlinear b').mpr hbM)
  · let := edgeGroup_isPerfect F hlinear
    rw [← Subgroup.commutator_eq_self (H := edgeGroup F hlinear)]
    exact commutator_mono (edgeGroup_le_pointLine F hlinear) (edgeGroup_le_pointLine F hlinear)

/-- The same intrinsic description inside the literal row normalizer. -/
theorem pointLine_relative_commutator :
    ⁅(sourcePlaneNormalizer F).subgroupOf (rowNormalizer F),
      (sourcePlaneNormalizer F).subgroupOf (rowNormalizer F)⁆ =
      (edgeGroup F hlinear).subgroupOf (rowNormalizer F) := by
  apply Subgroup.map_injective (rowNormalizer F).subtype_injective
  rw [map_commutator, subgroupOf_map_subtype, subgroupOf_map_subtype,
    inf_comm (sourcePlaneNormalizer F), pointLine_commutator,
    inf_eq_left.mpr ((edgeGroup_le_pointLine F hlinear).trans inf_le_left)]

variable {G' : Type*} [Group G'] [Finite G'] {z' : G'}
  (F' : MarkedCentralizer z') (hlinear' : F'.LinearFusion)

/-- A local row comparison preserving the actual point–line flag automatically
preserves the entire pointwise edge fixer, not just its quotient. -/
theorem row_equiv_edgeGroup
    (e : rowNormalizer F ≃* rowNormalizer F')
    (hP : ((sourcePlaneNormalizer F).subgroupOf (rowNormalizer F)).map e.toMonoidHom =
      (sourcePlaneNormalizer F').subgroupOf (rowNormalizer F')) :
    ((edgeGroup F hlinear).subgroupOf (rowNormalizer F)).map e.toMonoidHom =
      (edgeGroup F' hlinear').subgroupOf (rowNormalizer F') := by
  rw [← pointLine_relative_commutator F hlinear, map_commutator, hP,
    pointLine_relative_commutator F' hlinear']

/-- The previously constructed marked row isomorphism has the edge property
required for a source uniqueness-system similarity. -/
theorem exists_row_normalizer_edge_flag_equiv :
    ∃ e : rowNormalizer F ≃* rowNormalizer F',
      (((sourcePlaneNormalizer F).subgroupOf (rowNormalizer F)).map e.toMonoidHom =
        (sourcePlaneNormalizer F').subgroupOf (rowNormalizer F')) ∧
      (((sourceThreeSpaceNormalizer F).subgroupOf (rowNormalizer F)).map e.toMonoidHom =
        (sourceThreeSpaceNormalizer F').subgroupOf (rowNormalizer F')) ∧
      (((edgeGroup F hlinear).subgroupOf (rowNormalizer F)).map e.toMonoidHom =
        (edgeGroup F' hlinear').subgroupOf (rowNormalizer F')) := by
  obtain ⟨e, _, hP, hH, _⟩ := exists_row_normalizer_flag_equiv F F' hlinear hlinear'
  exact ⟨e, hP, hH, row_equiv_edgeGroup F hlinear F' hlinear' e hP⟩

end Theory.GroupTheory.TransvectionFive.UniquenessLinear.SourceGeometry
