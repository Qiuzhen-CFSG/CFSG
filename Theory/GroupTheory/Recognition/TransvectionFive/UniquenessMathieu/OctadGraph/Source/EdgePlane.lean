module
public import Theory.GroupTheory.Recognition.TransvectionFive.UniquenessMathieu.OctadGraph.Source.EdgeStructure
import all Theory.GroupTheory.Recognition.TransvectionFive.UniquenessMathieu.OctadGraph.Source.LinePlane

/-!
# The actual line–plane intersection in tensor coordinates

Inside the first rectangle, its intersection with A₂ is the marked
hyperplane in each of the two natural three-dimensional tensor rows.
Preserving this hyperplane is equivalent to normalizing A₂, by the proved
normalizer of the literal rectangle intersection. Hence the plane flag
inside the edge fixer is exactly a GL₃(2) hyperplane parabolic.

Source: Aschbacher, *Sporadic Groups* (1994), 41.4, p.222. The internal
import reuses the checked tensor-intersection and decomposition calculations
of the line–plane proof; no private names occur in exported statements.
-/

public noncomputable section
open Subgroup
namespace Theory.GroupTheory.TransvectionFive.UniquenessMathieu.OctadSource
open UniquenessLinear SourceNormalizer PlaneTensor PlaneCensus
open GraphUniquenessSystem GraphUniquenessSystem.Cosets

@[expose] def edgePlaneSubspace : Submodule (ZMod 2) (Fin 3 → ZMod 2) where
  carrier := {v | v 0 = 0}
  zero_mem' := rfl
  add_mem' := by intro a b ha hb; change a 0 + b 0 = 0; rw [ha, hb, zero_add]
  smul_mem' := by intro c v hv; change c * v 0 = 0; rw [hv, mul_zero]

variable {G : Type*} [Group G] [Finite G] {z : G} (F : MarkedCentralizer z) (D : LocalData F)

omit [Finite G] in
/-- The plane intersection is the same two-space in each tensor direction. -/
theorem tensor_element_mem_threeSpace_iff (i : Fin 3) (v : Fin 3 → ZMod 2) :
    element F (tensorCode i v) ∈ F.threeSpace ↔ v ∈ edgePlaneSubspace := by
  rw [plane_element_mem_threeSpace_iff]
  exact tensor_intersection i v

/-- Preserving the literal two-space in the three-dimensional tensor factor
preserves the actual source plane. -/
theorem line_linear_parabolic_mem_plane (n : planeNormalizer F)
    (hn : (planeQuotientEquiv F D.orientation.1 (QuotientGroup.mk n)).1 ∈
      BinaryLinear.parabolic edgePlaneSubspace) : (n : G) ∈ threeSpaceNormalizer F := by
  have hI : (n : G) ∈ normalizer ((F.plane ⊓ F.threeSpace : Subgroup G) : Set G) := by
    apply mem_normalizer_iff_map_conj_eq.mpr
    apply eq_of_le_of_card_ge
    · rintro _ ⟨a, ha, rfl⟩
      obtain ⟨x, hx⟩ := (sourceEquiv F).surjective ⟨a, ha.1⟩
      have hxa : element F x = a := congrArg Subtype.val hx
      obtain ⟨v, w, hvw, hzero⟩ := tensor_decomposition x
      have hz := hzero.mp ((plane_element_mem_threeSpace_iff F x).mp (hxa.symm ▸ ha.2))
      have he : (n : G) * a * (n : G)⁻¹ =
          element F (tensorCode (lineAction F D n 0)
            ((planeQuotientEquiv F D.orientation.1 (QuotientGroup.mk n)).1 v)) *
          element F (tensorCode (lineAction F D n 1)
            ((planeQuotientEquiv F D.orientation.1 (QuotientGroup.mk n)).1 w)) := by
        rw [← hxa, ← hvw, element_xor, lineAction_tensor, lineAction_tensor]
        group
      refine ⟨(mem_normalizer_iff.mp n.property a).mp ha.1, ?_⟩
      change (n : G) * a * (n : G)⁻¹ ∈ F.threeSpace
      rw [he]
      exact F.threeSpace.mul_mem
        ((tensor_element_mem_threeSpace_iff F _ _).mpr ((hn v).mpr hz.1))
        ((tensor_element_mem_threeSpace_iff F _ _).mpr ((hn w).mpr hz.2))
    · rw [card_map_of_injective (MulAut.conj (n : G)).injective]
  rw [planes_intersection_normalizer F (Or.inl D.orientation)] at hI
  exact hI.2

private theorem line_plane_preserves (n : planeNormalizer F) (hn : (n : G) ∈ threeSpaceNormalizer F)
    (v : Fin 3 → ZMod 2) (hv : v ∈ edgePlaneSubspace) :
    (planeQuotientEquiv F D.orientation.1 (QuotientGroup.mk n)).1 v ∈ edgePlaneSubspace := by
  have ha := (mem_normalizer_iff.mp hn (element F (tensorCode 0 v))).mp
    ((tensor_element_mem_threeSpace_iff F 0 v).mpr hv)
  rw [← lineAction_tensor F D n] at ha
  exact (tensor_element_mem_threeSpace_iff F _ _).mp ha

/-- The line–plane flag is exactly the parabolic of the marked tensor two-space. -/
theorem line_mem_plane_iff (n : planeNormalizer F) :
    (n : G) ∈ threeSpaceNormalizer F ↔
      (planeQuotientEquiv F D.orientation.1 (QuotientGroup.mk n)).1 ∈
        BinaryLinear.parabolic edgePlaneSubspace := by
  constructor
  · intro hn v
    constructor
    · intro hv
      have hh := line_plane_preserves F D n⁻¹ ((threeSpaceNormalizer F).inv_mem hn)
        ((planeQuotientEquiv F D.orientation.1 (QuotientGroup.mk n)).1 v) hv
      have hi : (QuotientGroup.mk n⁻¹ : planeQuotient F) = (QuotientGroup.mk n)⁻¹ :=
        by rfl
      rw [hi, map_inv] at hh
      change ((planeQuotientEquiv F D.orientation.1 (QuotientGroup.mk n)).1).symm
        ((planeQuotientEquiv F D.orientation.1 (QuotientGroup.mk n)).1 v) ∈ edgePlaneSubspace at hh
      rwa [LinearEquiv.symm_apply_apply] at hh
    · exact line_plane_preserves F D n hn v
  · exact line_linear_parabolic_mem_plane F D n

/-- In the actual edge group, plane stabilization is the marked tensor parabolic. -/
theorem edge_mem_plane_iff (a : edgeGroup F D) :
    (a : G) ∈ threeSpaceNormalizer F ↔
      edgeLinearAction F D a ∈ BinaryLinear.parabolic edgePlaneSubspace :=
  line_mem_plane_iff F D (inclusion (edgeFixer_le_line F D) a)

/-- The actual edge–plane intersection is the preimage through the literal action. -/
theorem edge_plane_parabolic_comap :
    (BinaryLinear.parabolic edgePlaneSubspace).comap (edgeLinearAction F D) =
      (threeSpaceNormalizer F).subgroupOf (edgeGroup F D) := by
  ext a
  exact (edge_mem_plane_iff F D a).symm

include D in
/-- The first rectangle is contained in the plane normalizer as an actual subgroup. -/
theorem rectangle_le_plane_normalizer : F.plane ≤ threeSpaceNormalizer F := by
  intro a ha
  let b : edgeGroup F D := ⟨a, rectangle_le_edgeGroup F D ha⟩
  apply (edge_mem_plane_iff F D b).mpr
  have hk : b ∈ (edgeLinearAction F D).ker := by
    rw [edgeLinearAction_kernel]
    exact ha
  rw [show edgeLinearAction F D b = 1 from hk]
  exact Subgroup.one_mem _

end Theory.GroupTheory.TransvectionFive.UniquenessMathieu.OctadSource
