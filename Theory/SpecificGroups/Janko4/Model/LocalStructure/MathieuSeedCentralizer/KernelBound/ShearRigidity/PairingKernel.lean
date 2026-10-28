module

public import Theory.SpecificGroups.Janko4.Model.LocalStructure.MathieuSeedCentralizer.KernelBound.ShearRigidity.PairingKernel.CheckedProducts
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.MathieuSeedCentralizer.KernelBound.ShearRigidity.PairingKernel.CheckedEquations
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.MathieuSeedCentralizer.KernelBound.ShearRigidity.PairingKernel.CheckedRecovery
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.MathieuSeedCentralizer.KernelBound.ShearRigidity.PairingKernel.CheckedSurvivors

/-!
# The complete two-dimensional shear pairing kernel

The 614 certified symmetry equations reconstruct every coefficient of the
616 candidate generators from two free coefficients. The two corresponding
matrix combinations are certified as identity and the published extra shear.
All arithmetic premises are discharged by ordinary Lean kernel reduction.

Source: `PairingKernel/source/README.md` and `ShearRigidity/source/README.md`.
-/

public section
open scoped Matrix
namespace Janko4.LocalStructure.MathieuSeedCentralizer.KernelBound.ShearRigidity

/-- Every candidate satisfying the Wall pairing constraint is a combination
of the identity and the second displayed shear. -/
theorem pairing_kernel (H : Coordinates.HalfMatrix) (hH : H ∈ candidateSpan)
    (hsym : (Coordinates.wallPairing * H)ᵀ = Coordinates.wallPairing * H) :
    ∃ a b : ZMod 2, H = a • (1 : Coordinates.HalfMatrix) + b • extraShear :=
  PairingCertificate.pairing_kernel_of_checks PairingCertificate.twistedChecks
    PairingCertificate.productChecks PairingCertificate.equationChecks
    PairingCertificate.recoveryChecks PairingCertificate.survivorChecks H hH hsym

end Janko4.LocalStructure.MathieuSeedCentralizer.KernelBound.ShearRigidity
