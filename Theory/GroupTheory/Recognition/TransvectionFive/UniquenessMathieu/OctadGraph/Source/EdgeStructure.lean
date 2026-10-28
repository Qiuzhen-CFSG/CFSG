module
public import Theory.GroupTheory.Recognition.TransvectionFive.UniquenessMathieu.OctadGraph.Source.Edges

/-!
# The actual source edge-fixer quotient

Line uniqueness identifies the ambient edge fixer with the kernel of the
three-point line action. Its remaining tensor factor gives a surjection to
GL₃(2) with kernel the literal A₁. The quotient map and conjugation on both
tensor rows are retained. Normalizing this edge fixer inside N_G(U₁) is
exactly preserving the marked point–line flag.

These are the edge-group and intersection ingredients in Aschbacher,
*Sporadic Groups* (1994), 41.4, printed p.222. No ambient comparison or
recognition conclusion is assumed.
-/

public noncomputable section
open Subgroup
namespace Theory.GroupTheory.TransvectionFive.UniquenessMathieu.OctadSource
open UniquenessLinear SourceNormalizer PlaneTensor PlaneCensus
open GraphUniquenessSystem GraphUniquenessSystem.Cosets
variable {G : Type*} [Group G] [Finite G] {z : G} (F : MarkedCentralizer z) (D : LocalData F)

/-- The actual pointwise fixer of the marked source edge. -/
abbrev edgeGroup := edgeFixer G (vertex (rowNormalizer F) 1)
  (vertex (rowNormalizer F) (lineSwap F D : G))

/-- The first rectangle lies in the actual edge fixer. -/
theorem rectangle_le_edgeGroup : F.plane ≤ edgeGroup F D := by
  intro a ha
  apply (line_edgeFixer_iff F D ⟨a, F.plane.le_normalizer ha⟩).mpr
  have hq : (QuotientGroup.mk (⟨a, F.plane.le_normalizer ha⟩ : planeNormalizer F) :
      planeQuotient F) = 1 := (QuotientGroup.eq_one_iff _).mpr ha
  change (planeQuotientEquiv F D.orientation.1 _).2 = 1
  change (planeQuotientEquiv F D.orientation.1 (QuotientGroup.mk (⟨a, F.plane.le_normalizer ha⟩ : planeNormalizer F))).2 = 1
  rw [hq, map_one]
  rfl

/-- The full ambient edge fixer acts by its actual three-dimensional tensor factor. -/
@[expose] def edgeLinearAction : edgeGroup F D →*
    ((Fin 3 → ZMod 2) ≃ₗ[ZMod 2] (Fin 3 → ZMod 2)) :=
  (MonoidHom.fst _ _).comp (((planeQuotientEquiv F D.orientation.1).toMonoidHom.comp
    (QuotientGroup.mk' _)).comp (inclusion (edgeFixer_le_line F D)))

/-- The literal rectangle quotient of an edge element has trivial line permutation. -/
theorem edge_tensor_image (a : edgeGroup F D) :
    planeQuotientEquiv F D.orientation.1
      (QuotientGroup.mk (inclusion (edgeFixer_le_line F D) a)) =
        (edgeLinearAction F D a, 1) := by
  apply Prod.ext
  · rfl
  · exact (line_edgeFixer_iff F D _).mp a.property

/-- The induced action on the first tensor factor is onto GL₃(2). -/
theorem edgeLinearAction_surjective : Function.Surjective (edgeLinearAction F D) := by
  intro f
  obtain ⟨q, hq⟩ := (planeQuotientEquiv F D.orientation.1).surjective (f, 1)
  obtain ⟨n, rfl⟩ := QuotientGroup.mk_surjective q
  have he : (n : G) ∈ edgeGroup F D := (line_edgeFixer_iff F D n).mpr (congrArg Prod.snd hq)
  exact ⟨⟨n, he⟩, congrArg Prod.fst hq⟩

/-- The kernel is the original A₁, retaining its literal inclusion in the edge fixer. -/
theorem edgeLinearAction_kernel :
    (edgeLinearAction F D).ker = F.plane.subgroupOf (edgeGroup F D) := by
  ext a
  change edgeLinearAction F D a = 1 ↔ (a : G) ∈ F.plane
  have he : edgeLinearAction F D a = 1 ↔
      planeQuotientEquiv F D.orientation.1
        (QuotientGroup.mk (inclusion (edgeFixer_le_line F D) a)) = 1 := by
    rw [edge_tensor_image]
    exact ⟨fun h => Prod.ext h rfl, fun h => congrArg Prod.fst h⟩
  rw [he, MulEquiv.map_eq_one_iff, QuotientGroup.eq_one_iff]
  rfl

instance rectangle_normal_edge : (F.plane.subgroupOf (edgeGroup F D)).Normal :=
  normal_subgroupOf_of_le_normalizer (edgeFixer_le_line F D)

/-- The actual edge-fixer quotient is GL₃(2), with its original denominator. -/
def edgeQuotientEquiv :
    (edgeGroup F D ⧸ F.plane.subgroupOf (edgeGroup F D)) ≃*
      ((Fin 3 → ZMod 2) ≃ₗ[ZMod 2] (Fin 3 → ZMod 2)) :=
  (QuotientGroup.quotientMulEquivOfEq (edgeLinearAction_kernel F D).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective (edgeLinearAction F D)
      (edgeLinearAction_surjective F D))

@[simp] theorem edgeQuotientEquiv_mk (a : edgeGroup F D) :
    edgeQuotientEquiv F D (QuotientGroup.mk a) = edgeLinearAction F D a := by rfl

/-- Both tensor rows retain the same original conjugation action of the edge fixer. -/
theorem edgeLinearAction_tensor (a : edgeGroup F D) (i : Fin 3) (v : Fin 3 → ZMod 2) :
    element F (tensorCode i (edgeLinearAction F D a v)) =
      (a : G) * element F (tensorCode i v) * (a : G)⁻¹ := by
  have he := lineAction_tensor F D (inclusion (edgeFixer_le_line F D) a) i v
  have hp := (line_edgeFixer_iff F D (inclusion (edgeFixer_le_line F D) a)).mp a.property
  rw [hp] at he
  exact he

/-- Inside the point stabilizer, the edge fixer's normalizer is the actual
point–line flag stabilizer. -/
theorem edgeGroup_normalizer_in_row :
    rowNormalizer F ⊓ normalizer (edgeGroup F D : Set G) =
      rowNormalizer F ⊓ planeNormalizer F := by
  apply le_antisymm
  · rintro g ⟨hr, hb⟩
    have hi := inf_normalizer_le_normalizer_inf ⟨hr, hb⟩
    rw [row_inf_edgeFixer F D, source_row_plane_normalizer] at hi
    exact hi
  · rintro g ⟨hr, hl⟩
    refine ⟨hr, ?_⟩
    apply mem_normalizer_iff.mpr
    intro b
    constructor
    · intro hb
      let n : planeNormalizer F := ⟨g, hl⟩
      let a : planeNormalizer F := ⟨b, edgeFixer_le_line F D hb⟩
      apply (line_edgeFixer_iff F D (n * a * n⁻¹)).mpr
      rw [map_mul, map_mul, map_inv, (line_edgeFixer_iff F D a).mp hb,
        mul_one, mul_inv_cancel]
    · intro hb
      have hbL : b ∈ planeNormalizer F := by
        have hh := (planeNormalizer F).mul_mem
          ((planeNormalizer F).mul_mem ((planeNormalizer F).inv_mem hl)
            (edgeFixer_le_line F D hb)) hl
        simpa only [mul_assoc, inv_mul_cancel_left, inv_mul_cancel_right, inv_mul_cancel, mul_one] using hh
      let n : planeNormalizer F := ⟨g, hl⟩
      let a : planeNormalizer F := ⟨b, hbL⟩
      have he := (line_edgeFixer_iff F D (n * a * n⁻¹)).mp hb
      rw [map_mul, map_mul, map_inv] at he
      have ha : lineAction F D a = 1 := by
        have hh := congrArg (fun p => (lineAction F D n)⁻¹ * p * lineAction F D n) he
        simpa only [mul_assoc, inv_mul_cancel_left, inv_mul_cancel_right, mul_one, inv_mul_cancel] using hh
      exact (line_edgeFixer_iff F D a).mpr ha

end Theory.GroupTheory.TransvectionFive.UniquenessMathieu.OctadSource
