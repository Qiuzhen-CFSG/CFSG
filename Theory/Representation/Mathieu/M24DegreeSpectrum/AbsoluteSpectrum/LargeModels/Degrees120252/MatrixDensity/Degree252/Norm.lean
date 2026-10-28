module

public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees120252.MatrixDensity.Data252
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees120252.MatrixDensity.Degree252.Norm.Compatibility
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees120252.MatrixDensity.Degree252.Norm.FrameCertificate
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees120252.MatrixDensity.Degree252.Norm.Reduction
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees120252.MatrixDensity.Degree252.Norm.Traversal
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees120252.MatrixDensity.Reduction

/-!
# The certified degree-252 norm and its density consumer

The checked algebraic reduction identifies the literal node-19 matrix with the
twenty-three-term polynomial in the product of the original generators. The
frame certificate and norm compatibility proofs discharge all five identities:
the generator product, right-row transitions, left inverse, seed sums and
commutation. Subalgebra closure then proves `norm_mem` without extra premises.

`full` applies the norm theorem to `matrix252_full_of_norm`, completing the
degree-252 matrix-algebra certificate. Neither result assumes irreducibility
or a native realization. The existing conditional `full_of_frame` is retained.

Source: node 19 of the unchanged `Degrees120252/source/density-252.json`, the
ATLAS matrices M24G1-f2r252B0, and the conventions and checked certificate
interfaces in `Norm/source/README.md`.
-/

public section
open Matrix
open Representation.MathieuSmall.M22Recognition.DegreeThirty.NineSubmodule.InducedHeads.HermitianFiltration.FactorAlgebras.Certificate
namespace Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees120252.MatrixDensity.Degree252
open Norm

/-- The literal norm node lies in every subalgebra containing the two generators. -/
theorem norm_mem (Q : Subalgebra (ZMod 2) (Matrix (Fin 252) (Fin 252) (ZMod 2)))
    (hA : ∀ j : Fin 2, matrix252 j ∈ Q) : matrix (n := 252) c19 ∈ Q :=
  norm_mem_of_frame generatorProduct_eq frame_steps frame_left_inverse
    norm_seed norm_commutes Q hA

/-- The checked norm discharges the last premise of the degree-252 density reduction. -/
theorem full (Q : Subalgebra (ZMod 2) (Matrix (Fin 252) (Fin 252) (ZMod 2)))
    (hA : ∀ j : Fin 2, matrix252 j ∈ Q) : Q = ⊤ :=
  matrix252_full_of_norm Q hA (norm_mem Q hA)

/-- The frame reduction supplies exactly the existing consumer's norm premise. -/
theorem full_of_frame
    (hproduct : generatorProduct = matrix252 0 * matrix252 1)
    (hstep : ∀ (s : Fin 11) (t : Fin 22),
      vecMul (orbitRow s t.val) generatorProduct = orbitRow s (t.val + 1))
    (hinverse : frameInverse * frame = 1)
    (hseed : ∀ s : Fin 11, vecMul (orbitRow s 0) normMatrix =
      ∑ t : Fin 23, orbitRow s t.val)
    (hcomm : generatorProduct * normMatrix = normMatrix * generatorProduct)
    (Q : Subalgebra (ZMod 2) (Matrix (Fin 252) (Fin 252) (ZMod 2)))
    (hA : ∀ j : Fin 2, matrix252 j ∈ Q) : Q = ⊤ :=
  matrix252_full_of_norm Q hA
    (norm_mem_of_frame hproduct hstep hinverse hseed hcomm Q hA)

end Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees120252.MatrixDensity.Degree252
