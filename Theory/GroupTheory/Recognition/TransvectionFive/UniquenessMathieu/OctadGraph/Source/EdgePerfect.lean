module
public import Theory.GroupTheory.Recognition.TransvectionFive.UniquenessMathieu.OctadGraph.Source.EdgeStructure
public import Theory.SpecificGroups.BinaryLinear.Perfect
public import Theory.GroupTheory.Commutator.PerfectQuotient
import all Theory.GroupTheory.Recognition.TransvectionFive.UniquenessLinearSourceTensorProduct
import all Theory.GroupTheory.Recognition.TransvectionFive.UniquenessMathieu.OctadGraph.Source.LinePlane

/-!
# The source edge fixer is intrinsic to the point–line stabilizer

The full GL₃(2) action expresses every vector in each tensor row as a
commutator. Thus A₁ lies in the derived subgroup of the edge fixer. Its
perfect GL₃(2) quotient then makes the whole edge fixer perfect. The
point–line stabilizer acts through a group of order two on the line, so its
derived subgroup is exactly this edge fixer. Consequently a row isomorphism
preserving the literal line flag also preserves the complete edge subgroup.

This adapts the checked linear-branch argument using only the actual
Mathieu 21-point tensor action. It supplies the edge-map clause of
Aschbacher, *Sporadic Groups* (1994), 41.4, printed p.222. The private imports
reuse the established tensor encoding and decomposition without exposing
implementation names or changing their public boundaries.
-/

public noncomputable section
open Subgroup
open scoped commutatorElement
namespace Theory.GroupTheory.TransvectionFive.UniquenessMathieu.OctadSource
open UniquenessLinear SourceNormalizer PlaneTensor PlaneCensus GraphUniquenessSystem GraphUniquenessSystem.Cosets
variable {G : Type*} [Group G] [Finite G] {z : G}
  (F : MarkedCentralizer z) (D : LocalData F)

private theorem tensor_add (i : Fin 3) (v w : Fin 3 → ZMod 2) :
    tensorCode i (v + w) = tensorCode i v ^^^ tensorCode i w := by decide +revert

private theorem tensor_zero (i : Fin 3) : tensorCode i 0 = 0 := by decide +revert

private theorem tensor_mem_commutator (i : Fin 3) (v : Fin 3 → ZMod 2) :
    (⟨element F (tensorCode i v), rectangle_le_edgeGroup F D (element_mem F _)⟩ :
      edgeGroup F D) ∈ commutator (edgeGroup F D) := by
  by_cases hv : v = 0
  · subst v
    have he : (⟨element F (tensorCode i 0), rectangle_le_edgeGroup F D (element_mem F _)⟩ :
        edgeGroup F D) = 1 := by
      apply Subtype.ext
      exact (congrArg (element F) (tensor_zero i)).trans (element_zero F)
    rw [he]
    exact (commutator (edgeGroup F D)).one_mem
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
  obtain ⟨n, hn⟩ := edgeLinearAction_surjective F D f
  let a : edgeGroup F D :=
    ⟨element F (tensorCode i w), rectangle_le_edgeGroup F D (element_mem F _)⟩
  have he : ⁅n, a⁆ = (⟨element F (tensorCode i v),
      rectangle_le_edgeGroup F D (element_mem F _)⟩ : edgeGroup F D) := by
    apply Subtype.ext
    change (n : G) * element F (tensorCode i w) * (n : G)⁻¹ *
      (element F (tensorCode i w))⁻¹ = element F (tensorCode i v)
    rw [← edgeLinearAction_tensor F D n i w, hn, hfw, tensor_add, element_xor]
    exact mul_inv_cancel_right _ _
  rw [← he]
  exact commutator_mem_commutator (mem_top _) (mem_top _)

theorem rectangle_le_edge_commutator :
    F.plane.subgroupOf (edgeGroup F D) ≤ commutator (edgeGroup F D) := by
  intro a ha
  obtain ⟨x, hx⟩ := (sourceEquiv F).surjective ⟨a, ha⟩
  have hxa : element F x = (a : G) := congrArg Subtype.val hx
  obtain ⟨v, w, hvw, _⟩ := tensor_decomposition x
  have hm := (commutator (edgeGroup F D)).mul_mem
    (tensor_mem_commutator F D 0 v) (tensor_mem_commutator F D 1 w)
  have he : (⟨element F (tensorCode 0 v), rectangle_le_edgeGroup F D (element_mem F _)⟩ :
      edgeGroup F D) *
    ⟨element F (tensorCode 1 w), rectangle_le_edgeGroup F D (element_mem F _)⟩ = a := by
    apply Subtype.ext
    change element F (tensorCode 0 v) * element F (tensorCode 1 w) = (a : G)
    rw [← element_xor, hvw, hxa]
  exact he ▸ hm

theorem edgeGroup_isPerfect : Group.IsPerfect (edgeGroup F D) := by
  let := BinaryLinear.linearGroup_isPerfect 3 (by decide)
  constructor
  have h := CentralExtension.ker_sup_commutator_eq_top_of_surjective
    (edgeLinearAction F D) (edgeLinearAction_surjective F D)
  rw [edgeLinearAction_kernel,
    sup_eq_right.mpr (rectangle_le_edge_commutator F D)] at h
  exact h

/-- The actual source edge fixer lies in its point–line flag stabilizer. -/
theorem edgeGroup_le_pointLine :
    edgeGroup F D ≤ rowNormalizer F ⊓ planeNormalizer F := by
  intro b hb
  refine ⟨?_, edgeFixer_le_line F D hb⟩
  have hx := hb.1
  change b ∈ MulAction.stabilizer G (vertex (rowNormalizer F) 1) at hx
  change b ∈ rowNormalizer F
  simpa only [stabilizer_base] using hx

/-- The edge fixer is intrinsic to the point–line stabilizer: its derived subgroup. -/
theorem pointLine_commutator :
    ⁅rowNormalizer F ⊓ planeNormalizer F,
      rowNormalizer F ⊓ planeNormalizer F⁆ = edgeGroup F D := by
  apply le_antisymm
  · apply commutator_le.mpr
    rintro a ⟨haM, haP⟩ b ⟨hbM, hbP⟩
    let a' : planeNormalizer F := ⟨a, haP⟩
    let b' : planeNormalizer F := ⟨b, hbP⟩
    apply (line_edgeFixer_iff F D ⁅a', b'⁆).mpr
    rw [map_commutatorElement]
    apply commutatorElement_eq_one_iff_mul_comm.mpr
    exact (by decide : ∀ p q : Equiv.Perm (Fin 3), p 0 = 0 → q 0 = 0 → p * q = q * p)
      _ _ ((lineAction_fix_iff F D a').mpr haM)
      ((lineAction_fix_iff F D b').mpr hbM)
  · let := edgeGroup_isPerfect F D
    rw [← Subgroup.commutator_eq_self (H := edgeGroup F D)]
    exact commutator_mono (edgeGroup_le_pointLine F D) (edgeGroup_le_pointLine F D)

/-- The same intrinsic description inside the literal row normalizer. -/
theorem pointLine_relative_commutator :
    ⁅(planeNormalizer F).subgroupOf (rowNormalizer F),
      (planeNormalizer F).subgroupOf (rowNormalizer F)⁆ =
      (edgeGroup F D).subgroupOf (rowNormalizer F) := by
  apply Subgroup.map_injective (rowNormalizer F).subtype_injective
  rw [map_commutator, subgroupOf_map_subtype, subgroupOf_map_subtype,
    inf_comm (planeNormalizer F), pointLine_commutator,
    inf_eq_left.mpr ((edgeGroup_le_pointLine F D).trans inf_le_left)]

variable {G' : Type*} [Group G'] [Finite G'] {z' : G'}
  (F' : MarkedCentralizer z') (D' : LocalData F')

/-- A local row comparison preserving the actual point–line flag automatically
preserves the entire pointwise edge fixer, not just its quotient. -/
theorem row_equiv_edgeGroup
    (e : rowNormalizer F ≃* rowNormalizer F')
    (hP : ((planeNormalizer F).subgroupOf (rowNormalizer F)).map e.toMonoidHom =
      (planeNormalizer F').subgroupOf (rowNormalizer F')) :
    ((edgeGroup F D).subgroupOf (rowNormalizer F)).map e.toMonoidHom =
      (edgeGroup F' D').subgroupOf (rowNormalizer F') := by
  rw [← pointLine_relative_commutator F D, map_commutator, hP,
    pointLine_relative_commutator F' D']

end Theory.GroupTheory.TransvectionFive.UniquenessMathieu.OctadSource
