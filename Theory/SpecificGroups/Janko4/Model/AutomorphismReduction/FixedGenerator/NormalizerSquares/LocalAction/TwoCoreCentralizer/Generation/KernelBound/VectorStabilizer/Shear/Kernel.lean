module

public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.Generation.KernelBound.VectorStabilizer.Shear.Kernel.CheckedBase
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.Generation.KernelBound.VectorStabilizer.Shear.Kernel.CheckedFirst
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.Generation.KernelBound.VectorStabilizer.Shear.Kernel.CheckedRecovery
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.Generation.KernelBound.VectorStabilizer.Shear.Kernel.CheckedFinal

/-!
# The complete shear coefficient kernel

For every symmetric parameter, the two actual upper-block test effects lying
in the actual thirteen-generator radical span force a scalar multiple of the
identity-shear parameter. The proof certifies all 1275 → 63 → 1 reconstruction
steps and their connection to the concrete matrices.

Source: Shear/source/README.md and Kernel/source/README.md. No group-element,
exterior-stabilizer or radical-upper-bound premise is used here.
-/

public section
namespace Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.Generation.KernelBound.VectorStabilizer.Shear

/-- The simultaneous coefficient kernel of the two literal shear tests. -/
theorem coefficient_kernel (x : Parameter)
    (hx : ∀ t : Fin 2, testEffect t x ∈ radicalKUpperSpace) :
    ∃ a : ZMod 2, x = a • finalParameter :=
  KernelCertificate.kernel_of_checks KernelCertificate.baseChecks
    KernelCertificate.firstChecks KernelCertificate.firstRecoveryChecks
    KernelCertificate.secondChecks KernelCertificate.secondRecoveryChecks
    KernelCertificate.finalChecks x hx

end Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.Generation.KernelBound.VectorStabilizer.Shear
