module

public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Projective

/-!
# Projective general linear group in dimension two

The concrete `PGL(2, K)` matrix-group model, copied from
`GorensteinWalter.Classification.PGL2` and exposed as `PGL2`.
-/

universe u

/-- `PGL(2, K)`. -/
public abbrev PGL2 (K : Type u) [CommRing K] :=
  Matrix.ProjGenLinGroup (Fin 2) K
