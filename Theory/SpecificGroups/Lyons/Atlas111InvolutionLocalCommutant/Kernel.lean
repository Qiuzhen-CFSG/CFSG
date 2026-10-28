module

public import Theory.SpecificGroups.Lyons.Atlas111InvolutionLocalCommutant.Reduction
public import Theory.SpecificGroups.Lyons.Atlas111InvolutionLocalCommutant.Words
public import Theory.SpecificGroups.Lyons.Atlas111InvolutionLocalCommutant.Kernel.Polynomial
public import Theory.SpecificGroups.Lyons.Atlas111InvolutionLocalCommutant.Kernel.Reconstruction

/-!
# Two-dimensional annihilator kernel for the literal Lyons local generators

The certified word polynomial annihilates the seed. Its first 109 rows, followed
by coordinate rows 0 and 2, have a certified left inverse. The inverse's last two
columns reconstruct every kernel vector in the span of the seed and its image
under the involution. All finite arithmetic is checked by Lean's kernel.

Sources: the literal ATLAS program `LyG1-max4W1` and matrices attributed in
`Atlas111InvolutionSource/` and `Atlas111Source/`. Reproducible candidate generation
and the retained search data are in `Kernel/source/`.
-/

namespace Lyons.SimplicityCertificate

/-- The explicit annihilator has kernel contained in the expected two-dimensional span. -/
public theorem involutionLocal_kernel_certificate : InvolutionLocalKernelCertificate :=
  LocalCommutant.Kernel.certificate_of_polynomial LocalCommutant.Kernel.polynomial_eq

end Lyons.SimplicityCertificate
