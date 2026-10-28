module

public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.Generation.KernelBound.VectorStabilizer.Shear.Geometry
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.Generation.KernelBound.VectorStabilizer.Shear.Parameters
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.Generation.KernelBound.VectorStabilizer.Shear.Forms
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.Generation.KernelBound.VectorStabilizer.Shear.Kernel

/-!
# Assembly of the final shear from its finite certificates

The geometric part proves symmetry of J C and places both pullback differences
in the actual radical-K upper span. Exhaustive symmetric coordinates reduce the
remaining assertion to a concrete coefficient kernel. The two finite certificate
premises in the reusable conditional assembly are discharged by the selected
form and complete coefficient-kernel certificates. Thus the final shear is zero
or the identity under exactly the stated radical, form and block hypotheses.

Source and witness conventions: source/README.md and Shear/source/README.md.
-/

public section
open scoped Matrix
namespace Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.Generation.KernelBound.VectorStabilizer
open OrbitCoverCoordinates OrbitCoverCoordinates.LinearMembership

/-- Assemble the exact shear implication after the two selected-form checks
and the complete coefficient-kernel computation have been proved. -/
theorem shear_eq_zero_or_one_of_certificates
    (hforms : ∀ t : Fin 2,
      Shear.testForm t ∈ exteriorFormSpace ∧
      restrictionEmbeddingᵀ * Shear.testForm t * restrictionEmbedding = 0 ∧
      restrictionEmbeddingᵀ * Shear.testForm t * mixedEmbedding = 0 ∧
      restrictionEmbeddingᵀ * Shear.testForm t * restrictionLifts = Shear.testIU t)
    (hkernel : ∀ x : Shear.Parameter,
      (∀ t : Fin 2, Shear.testEffect t x ∈ radicalKUpperSpace) →
      ∃ a : ZMod 2, x = a • Shear.finalParameter)
    (hrad : RadicalKUpperBound) (g : BinaryMatrixˣ) (hker : KernelConditions g)
    (hform : formPullback g invariantForm = invariantForm)
    (hext : g ∈ formStabilizer exteriorFormSpace)
    (hS : restrictionMatrix g = 1) (hD : middleRightBlock g = 0)
    (hB : upperMiddleBlock g = 0) :
    upperRightBlock g = 0 ∨ upperRightBlock g = 1 := by
  obtain ⟨x, hx⟩ := Shear.exists_parameter (upperRightBlock g)
    (shear_pairing_symmetric g hker hform hS hD)
  have htests : ∀ t : Fin 2, Shear.testEffect t x ∈ radicalKUpperSpace := by
    intro t
    obtain ⟨hR, hEE, hEH, hIU⟩ := hforms t
    have ht : (Shear.testForm t)ᵀ = Shear.testForm t :=
      decodeExteriorForm_transpose _
    have h := shear_test_mem_upper hrad g hker hext hS hD hB
      (Shear.testForm t) hR ht hEE hEH
    rw [hIU] at h
    simpa only [Shear.testEffect, hx] using h
  obtain ⟨a, ha⟩ := hkernel x htests
  have h := Shear.shearOfParameter_scalar_final a
  rwa [← ha, hx] at h

/-- The remaining shear of a form-preserving kernel element is zero or the
identity. The selected exterior forms and the complete symmetric coefficient
kernel are certified; the radical bound and preceding block reductions remain
the explicit inputs supplied by the enclosing vector-stabilizer argument. -/
theorem shear_eq_zero_or_one
    (hrad : RadicalKUpperBound) (g : BinaryMatrixˣ) (hker : KernelConditions g)
    (hform : formPullback g invariantForm = invariantForm)
    (hext : g ∈ formStabilizer exteriorFormSpace)
    (hS : restrictionMatrix g = 1) (hD : middleRightBlock g = 0)
    (hB : upperMiddleBlock g = 0) :
    upperRightBlock g = 0 ∨ upperRightBlock g = 1 :=
  shear_eq_zero_or_one_of_certificates Shear.testForm_spec Shear.coefficient_kernel
    hrad g hker hform hext hS hD hB

end Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.Generation.KernelBound.VectorStabilizer
