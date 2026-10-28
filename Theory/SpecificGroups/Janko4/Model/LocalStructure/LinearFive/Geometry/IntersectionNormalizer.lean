module
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.LinearFive.Geometry.KernelOrbit
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.ElementaryNormalizerCover.TwoConjugateReduction

/-!
# The full normalizer of the actual two-F intersection lies in max1

The intersection contains the native mask-51 involution, whose full centralizer
lies in max1. Since the intersection lies in E, the proved uniqueness of E in
max1 controls its full ambient normalizer. This instantiates the intersection
clause used in the F branch of Kleidman--Wilson (1988), Proposition 2.2.3, p.491.
The global two-occurrence catalogue and the source centralizer placement of X
remain separate inputs to that branch.
-/

public noncomputable section
namespace Janko4.LocalStructure.LinearFive.Geometry
open Cardinality KernelCount Subgroup
attribute [local irreducible] modelGroup matrixA matrixB max1Subgroup localKernel localX localY

theorem centralizer_secondF : centralizer (secondF : Set Model) = secondF := by
  let e := MulAut.conj seed
  apply le_antisymm
  · intro x hx
    refine mem_map.mpr ⟨e.symm x, ?_, e.apply_symm_apply x⟩
    rw [← centralizer_F]
    intro y hy
    apply e.injective
    simpa only [map_mul, e.apply_symm_apply] using hx (e y) (mem_map_of_mem _ hy)
  · have hh := map_centralizer_le_centralizer_image (F : Set Model) e.toMonoidHom
    simpa only [centralizer_F, Subgroup.coe_map, e, secondF] using hh

/-- The actual intersection has its full centralizer inside max1. -/
theorem centralizer_intersection_le_M : centralizer (F ⊓ secondF : Set Model) ≤ M := by
  apply le_trans ?_ centralizer_kernel51_le_M
  apply centralizer_le
  rintro x (rfl : x = (kernelValue 51 : Model))
  change (kernelValue 51 : Model) ∈ F ⊓ secondF
  rw [intersection_eq]
  exact ⟨generator_mem_F 0, kernelValue_mem_E 51⟩

/-- E-uniqueness applies to the actual intersection of our two F-conjugates.
This discharges the intersection-normalizer clause in the KW 2.2.3 argument. -/
theorem normalizer_intersection_le_M : normalizer (F ⊓ secondF : Set Model) ≤ M :=
  ElementaryNormalizerCover.normalizer_le_mathieu_of_kernel_and_centralizer
    _ intersection_le_E centralizer_intersection_le_M

/-- The literal native pair supplies the source intersection data, together
with the centralizer and normalizer bounds actually consumed by the cover. -/
theorem native_pair_geometry :
    F ≤ D ∧ secondF ≤ D ∧ F ≠ secondF ∧
      Nat.card (F ⊓ secondF : Subgroup Model) = 64 ∧ F ⊓ secondF ≤ E ∧
      centralizer (secondF : Set Model) = secondF ∧
      normalizer (F ⊓ secondF : Set Model) ≤ M :=
  ⟨F_le_Q.trans Q_le_D,secondF_le_Q.trans Q_le_D,secondF_ne,intersection_card,
    intersection_le_E,centralizer_secondF,normalizer_intersection_le_M⟩

end Janko4.LocalStructure.LinearFive.Geometry
