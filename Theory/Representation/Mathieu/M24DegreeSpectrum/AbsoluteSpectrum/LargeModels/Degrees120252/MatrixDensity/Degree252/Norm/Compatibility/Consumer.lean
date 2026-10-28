module

public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees120252.MatrixDensity.Degree252.Norm.Compatibility
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees120252.MatrixDensity.Degree252.Norm

/-!
# The norm compatibility identities in their existing consumers

Apply the unconditional seed and commutation identities to `norm_mem_of_frame`
and `Degree252.full_of_frame`. Only the three independent frame-certificate
identities remain explicit. This module is separate so the final norm assembly
can import `Compatibility` without an import cycle.

Source: the literal node-19 reduction documented in `Norm/source/README.md`.
-/

public section
open Matrix
open Representation.MathieuSmall.M22Recognition.DegreeThirty.NineSubmodule.InducedHeads.HermitianFiltration.FactorAlgebras.Certificate
namespace Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees120252.MatrixDensity.Degree252
namespace Norm

/-- Discharge the two compatibility premises of the existing norm reduction. -/
theorem norm_mem_of_compatible_frame
    (hproduct : generatorProduct = matrix252 0 * matrix252 1)
    (hstep : ∀ (s : Fin 11) (t : Fin 22),
      vecMul (orbitRow s t.val) generatorProduct = orbitRow s (t.val + 1))
    (hinverse : frameInverse * frame = 1)
    (Q : Subalgebra (ZMod 2) (Mat 252))
    (hA : ∀ j : Fin 2, matrix252 j ∈ Q) : matrix (n := 252) c19 ∈ Q :=
  norm_mem_of_frame hproduct hstep hinverse norm_seed norm_commutes Q hA

end Norm

open Norm

/-- The density application now needs only the independent frame certificate. -/
theorem full_of_compatible_frame
    (hproduct : generatorProduct = matrix252 0 * matrix252 1)
    (hstep : ∀ (s : Fin 11) (t : Fin 22),
      vecMul (orbitRow s t.val) generatorProduct = orbitRow s (t.val + 1))
    (hinverse : frameInverse * frame = 1)
    (Q : Subalgebra (ZMod 2) (Mat 252))
    (hA : ∀ j : Fin 2, matrix252 j ∈ Q) : Q = ⊤ :=
  full_of_frame hproduct hstep hinverse norm_seed norm_commutes Q hA

end Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees120252.MatrixDensity.Degree252
