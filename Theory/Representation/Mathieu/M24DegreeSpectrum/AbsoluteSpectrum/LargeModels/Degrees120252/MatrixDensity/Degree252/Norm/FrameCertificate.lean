module

public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees120252.MatrixDensity.Degree252.Norm.FrameCertificate.GeneratorProduct
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees120252.MatrixDensity.Degree252.Norm.FrameCertificate.Steps
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees120252.MatrixDensity.Degree252.Norm.FrameCertificate.LeftInverse
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees120252.MatrixDensity.Degree252.Norm.Reduction

/-!
# Certified Krylov frame for the degree-252 norm

The literal generator product, all 242 right-row transitions, and the left
inverse of the first 252 stored rows are certified without further premises.
The final theorem supplies these identities to `norm_mem_of_frame`; only the
two independently owned norm compatibility identities remain explicit.

Source: `Degrees120252/source/density-252.json`, the constants in `Norm.Frame`,
and the conventions in `Norm/source/README.md`. The finite arithmetic checker
and its regeneration instructions are documented in `FrameCertificate/source`.
-/

public section
open Matrix
namespace Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees120252.MatrixDensity.Degree252.Norm

/-- Discharge the three frame premises of the published norm reduction. -/
theorem norm_mem_of_compatibility
    (hseed : ∀ s : Fin 11, vecMul (orbitRow s 0) normMatrix =
      ∑ t : Fin 23, orbitRow s t.val)
    (hcomm : generatorProduct * normMatrix = normMatrix * generatorProduct)
    (Q : Subalgebra (ZMod 2) (Matrix (Fin 252) (Fin 252) (ZMod 2)))
    (hA : ∀ j : Fin 2, matrix252 j ∈ Q) : normMatrix ∈ Q :=
  norm_mem_of_frame generatorProduct_eq frame_steps frame_left_inverse hseed hcomm Q hA

end Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees120252.MatrixDensity.Degree252.Norm
