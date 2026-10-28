module

public import Theory.SpecificGroups.Janko4.Model.LocalStructure.MathieuSeedCentralizer.KernelBound.AmbientConditions
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.MathieuSeedCentralizer.KernelBound.RestrictionRigidity.LocalElements
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.MathieuSeedCentralizer.KernelBound.RestrictionRigidity.Normalization
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.MathieuSeedCentralizer.KernelBound.RestrictionRigidity.Separation
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.MathieuSeedCentralizer.KernelBound.RestrictionRigidity.TopOperator

/-!
# Matching algebra-valued restrictions with actual kernel elements

An algebra-valued restriction is divided by an actual local-kernel
restriction so that it has the form `1 + D` in the displayed square span.
Preservation of the actual restriction space then puts the linear pullback
term in the sum of that space with all quadratic basis terms. A linear
separation certificate leaves only the top-operator line. Its quadratic term
vanishes by `TopOperator`, so a nonzero linear residue rejects that line.
Multiplying back recovers the restriction of an actual local-kernel element.

The conditional reductions retain their explicit finite premises. The final
theorem discharges all four using `Normalization` and `Separation`, proving
restriction matching for every algebra-valued element of the full ambient
seed centralizer.

Source: the complete finite route in `KernelBound/source/README.md` and
`Scratch/J4FleetGuidance/SeedCentralizer/kernel_restriction.py`.
-/

public section
namespace Janko4.LocalStructure.MathieuSeedCentralizer.KernelBound
open Coordinates RestrictionRigidity

/-- The quadratic reduction applies to the full centralizer using its actual
restriction-space invariant; no extra form-preservation premise is required. -/
theorem normalized_restriction_eq_one_of_separation
    (hTest : testForm ∈ restrictionSpace)
    (hSeparate : ∀ D ∈ squareSpan,
      linearTerm testForm D ∈ restrictionSpace ⊔ quadraticSpan testForm squareBasis →
        ∃ a : ZMod 2, D = a • topOperator)
    (hReject : linearTerm testForm topOperator ∉ restrictionSpace)
    (c : SeedCentralizer) (D : HalfMatrix) (hD : D ∈ squareSpan)
    (hc : restriction c = 1 + D) : restriction c = 1 := by
  have hp := centralizer_preserves_restrictionSpace c testForm hTest
  rw [hc] at hp
  have hz : D = 0 := eq_zero_of_separation testForm squareBasis restrictionSpace topOperator
    hTest hSeparate topOperator_quadraticTerm hReject hD hp
  simpa only [hz, add_zero] using hc

/-- Conditional assembly; its four finite premises are not source assumptions. -/
theorem exists_ambientKernel_same_restriction_of_certificates
    (hNormalize : ∀ c : SeedCentralizer, restriction c ∈ concreteAlgebra →
      ∃ (e : ambientKernel) (D : HalfMatrix), D ∈ squareSpan ∧
        restriction ((kernelCentralizerInclusion e)⁻¹ * c) = 1 + D)
    (hTest : testForm ∈ restrictionSpace)
    (hSeparate : ∀ D ∈ squareSpan,
      linearTerm testForm D ∈ restrictionSpace ⊔ quadraticSpan testForm squareBasis →
        ∃ a : ZMod 2, D = a • topOperator)
    (hReject : linearTerm testForm topOperator ∉ restrictionSpace)
    (c : SeedCentralizer) (hc : restriction c ∈ concreteAlgebra) :
    ∃ e : ambientKernel, restriction (kernelCentralizerInclusion e) = restriction c := by
  obtain ⟨e, D, hD, hd⟩ := hNormalize c hc
  have hfix := normalized_restriction_eq_one_of_separation hTest hSeparate hReject
    ((kernelCentralizerInclusion e)⁻¹ * c) D hD hd
  refine ⟨e, ?_⟩
  calc
    restriction (kernelCentralizerInclusion e) =
        restriction (kernelCentralizerInclusion e) *
          restriction ((kernelCentralizerInclusion e)⁻¹ * c) := by rw [hfix, mul_one]
    _ = restriction (kernelCentralizerInclusion e * ((kernelCentralizerInclusion e)⁻¹ * c)) :=
      (map_mul restriction _ _).symm
    _ = restriction c := by rw [mul_inv_cancel_left]

/-- Every algebra-valued restriction of the full ambient seed centralizer is
the restriction of an actual element of the known ambient local kernel. -/
theorem exists_ambientKernel_same_restriction (c : SeedCentralizer)
    (hc : restriction c ∈ concreteAlgebra) :
    ∃ e : ambientKernel, restriction (kernelCentralizerInclusion e) = restriction c :=
  exists_ambientKernel_same_restriction_of_certificates exists_kernel_normalization
    testForm_mem_restrictionSpace linearTerm_mem_sup_implies_top
    topOperator_linearTerm_not_mem c hc

end Janko4.LocalStructure.MathieuSeedCentralizer.KernelBound
