module

public import Theory.SpecificGroups.Janko4.Model.LocalStructure.MathieuSeedCentralizer.IntrinsicAlgebra.RadicalCertificate.Coordinates
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.MathieuSeedCentralizer.IntrinsicAlgebra.RadicalCertificate.RawSpace
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.MathieuSeedCentralizer.IntrinsicAlgebra.RadicalCertificate.CoefficientElimination.Evaluations
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.MathieuSeedCentralizer.IntrinsicAlgebra.RadicalCertificate.CoefficientElimination.Recovery

/-!
# Exhaustive elimination of the raw radical equations

The 1211 selected entries of Kᵀ R give a certified coefficient matrix T on
the original 1221 exterior forms. A checked recovery matrix satisfies
D T = 1 + K₀ F, where K₀ contains precisely the ten literal radical coefficient
words and F selects their prescribed free coordinates. Thus every form with
R K = 0 has exactly those ten coordinates, proving the unconditional containment.

No rank, completeness, or group-theoretic hypothesis is assumed. Numerical
witnesses and their provenance are documented in
`CoefficientElimination/source/README.md`; all checks use kernel reduction.
-/

public section
open scoped Matrix
namespace Janko4.LocalStructure.MathieuSeedCentralizer.IntrinsicAlgebra
open OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.Generation.KernelBound.OrbitCoverCoordinates

set_option maxRecDepth 10000 in
/-- Exhaustive reconstruction in the original exterior coefficient family. -/
theorem rawRadical_coefficient_reconstruction (c : Fin 1221 → ZMod 2)
    (hc : (∑ j, c j • exteriorBasisForm j) * kernelColumns = 0) (j : Fin 1221) :
    c j = ∑ i : Fin 10, c (radicalCoordinateIndex i) *
      bit (radicalCoefficients.get i) j.val := by
  have hR : (∑ j, c j • exteriorBasisForm j) ∈ rawRadicalForms := by
    refine ⟨?_, hc⟩
    exact ambientForms.sum_mem (fun j _ => ambientForms.smul_mem _ (exteriorBasisForm_mem j))
  apply CoefficientElimination.kernel_of_checks CoefficientElimination.allRowChecks c _ j
  rw [← CoefficientElimination.selectedEvaluation_sum CoefficientElimination.allEvaluations c]
  exact CoefficientElimination.selectedEvaluation_zero hR

/-- Every raw radical form belongs to the span of the exact ten saved forms. -/
theorem rawRadicalForms_le_rawRadicalSpan : rawRadicalForms ≤ rawRadicalSpan := by
  intro R hR
  apply mem_rawRadicalSpan_of_coordinates hR.1
  apply rawRadical_coefficient_reconstruction
  rw [ambientForm_reconstruction hR.1]
  exact hR.2

end Janko4.LocalStructure.MathieuSeedCentralizer.IntrinsicAlgebra
