module

public import Theory.SpecificGroups.Lyons.Atlas111InvolutionLocalCommutant.Reduction

/-!
# Concrete certificates for the Lyons involution-local commutant

The two contracts below specialize cyclic-vector reconstruction to the literal
outputs of the ATLAS program `LyG1-max4W1`. A cyclic orbit basis determines a
commuting matrix from its seed column, and an annihilating word polynomial
restricts that column to the span of the seed and its involution image.

Source: `Atlas111InvolutionSource/` and `Atlas111Source/`.
-/

namespace Lyons.SimplicityCertificate

/-- The two finite certificates suffice for the exact commutant contract. -/
public theorem involutionLocal_commutant_of_certificates
    (hc : InvolutionLocalCyclicCertificate) (hk : InvolutionLocalKernelCertificate) :
    InvolutionLocalCommutantCertificate :=
  LocalCommutant.commutant_of_cyclic_kernel _ _ _ hc hk

end Lyons.SimplicityCertificate
