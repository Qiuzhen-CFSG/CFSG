module

public import Theory.SpecificGroups.Janko4.Model.LocalStructure.MathieuSeedCentralizer.IntrinsicAlgebra.RadicalCertificate.CoefficientElimination
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.MathieuSeedCentralizer.IntrinsicAlgebra.RadicalCertificate.Transport

/-!
# Complete radical coordinates and the intrinsic basis

The exhaustive coefficient calculation and the ten annihilation certificates
identify the raw radical space with the span of the exact saved matrices.
Their independence gives dimension ten. Transport to `radicalForms` requires
only that the saved kernel columns span the actual displacement kernel;
the completeness premise of `Transport` is discharged here.

Source: `IntrinsicAlgebra/source/README.md` and the literal seed calculation
in `Scratch/J4FleetGuidance/SeedCentralizer/explore.py` in the source checkout.
The kernel-range identification remains the separate geometry obligation.
-/

public section
open scoped Matrix
namespace Janko4.LocalStructure.MathieuSeedCentralizer.IntrinsicAlgebra

/-- The raw column condition is exhausted by the ten literal radical forms. -/
theorem rawRadicalForms_eq_rawRadicalSpan : rawRadicalForms = rawRadicalSpan :=
  le_antisymm rawRadicalForms_le_rawRadicalSpan rawRadicalSpan_le_rawRadicalForms

/-- Exact radical-coordinate criterion inside the original exterior space. -/
theorem mul_kernelColumns_eq_zero_iff_mem_rawRadicalSpan {R : BinaryMatrix}
    (hR : R ∈ ambientForms) :
    R * kernelColumns = 0 ↔ R ∈ rawRadicalSpan := by
  rw [← rawRadicalForms_eq_rawRadicalSpan, mem_rawRadicalForms]
  exact ⟨fun h => ⟨hR, h⟩, And.right⟩

theorem finrank_rawRadicalForms : Module.finrank (ZMod 2) rawRadicalForms = 10 := by
  rw [rawRadicalForms_eq_rawRadicalSpan]
  exact finrank_rawRadicalSpan

/-- The only transport premise identifies the actual kernel with the saved columns. -/
theorem radicalForms_eq_rawRadicalSpan
    (hK : kernelSpace = LinearMap.range kernelColumns.mulVecLin) :
    radicalForms = rawRadicalSpan := by
  rw [radicalForms_eq_rawRadicalForms hK, rawRadicalForms_eq_rawRadicalSpan]

/-- The exact ten ambient matrices form a basis of the actual radical space
once the saved kernel columns are identified with the displacement kernel. -/
noncomputable def radicalBasis
    (hK : kernelSpace = LinearMap.range kernelColumns.mulVecLin) :
    Module.Basis (Fin 10) (ZMod 2) radicalForms :=
  radicalBasisOfRawCompleteness rawRadicalForms_le_rawRadicalSpan hK

theorem radicalBasis_apply
    (hK : kernelSpace = LinearMap.range kernelColumns.mulVecLin) (i : Fin 10) :
    (radicalBasis hK i : BinaryMatrix) = ambientRadicalForm i :=
  radicalBasisOfRawCompleteness_apply rawRadicalForms_le_rawRadicalSpan hK i

theorem finrank_radicalForms
    (hK : kernelSpace = LinearMap.range kernelColumns.mulVecLin) :
    Module.finrank (ZMod 2) radicalForms = 10 :=
  finrank_radicalForms_of_rawCompleteness rawRadicalForms_le_rawRadicalSpan hK

end Janko4.LocalStructure.MathieuSeedCentralizer.IntrinsicAlgebra
