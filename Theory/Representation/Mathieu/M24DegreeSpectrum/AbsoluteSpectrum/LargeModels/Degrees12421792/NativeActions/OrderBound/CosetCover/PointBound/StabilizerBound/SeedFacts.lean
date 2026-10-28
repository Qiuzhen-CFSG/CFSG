module

public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.OrderBound.CosetCover.PointBound.StabilizerBound.Data

/-!
# Initial exact identities for the comparison certificates

Three original generators are trivial by literal one-letter Schreier relators.
The second comparison relator is a free cancellation because the proposed
first and third generators are the same word. These facts are independent of
the remaining comparison relations and generation certificate.
Source: `Stabilizer.relatorLetters` and `Comparison.generatorWord`.
-/

public section
namespace Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Presentation.OrderBound.CosetCover.PointSchreier.PointBound.Stabilizer.Comparison
open Subgroup.CosetWordCertificate
open Janko4.Cardinality.QuotientCount.UpperBound.PresentationBound.StabilizerChain

theorem original_generator_zero : (PresentedGroup.of (0 : Fin 24) : Presented) = 1 := by
  have h := defining_relation (0, 1)
  change (PresentedGroup.of (0 : Fin 24) : Presented)⁻¹ * 1 = 1 at h
  simpa only [mul_one, inv_eq_one] using h

theorem original_generator_six : (PresentedGroup.of (6 : Fin 24) : Presented) = 1 := by
  have h := defining_relation (3, 1)
  change (PresentedGroup.of (6 : Fin 24) : Presented)⁻¹ * 1 = 1 at h
  simpa only [mul_one, inv_eq_one] using h

theorem original_generator_sixteen : (PresentedGroup.of (16 : Fin 24) : Presented) = 1 := by
  have h := defining_relation (12, 1)
  change (PresentedGroup.of (16 : Fin 24) : Presented)⁻¹ * 1 = 1 at h
  simpa only [mul_one, inv_eq_one] using h

theorem relation_one : eval generator (level2Relator 1) = 1 := by
  change (generator 0)⁻¹ * (generator 0 * 1) = 1
  simp only [mul_one, inv_mul_cancel]

end Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Presentation.OrderBound.CosetCover.PointSchreier.PointBound.Stabilizer.Comparison
