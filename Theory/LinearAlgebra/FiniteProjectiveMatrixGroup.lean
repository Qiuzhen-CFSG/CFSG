module

public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Projective

/-!
# Finiteness of projective matrix groups

Over a finite coefficient ring, the general linear group is finite, so its
quotient by the center is finite. This exposes that fact through Mathlib's
projective carrier, allowing finite projective isometry subgroups to inherit it.

The construction is the central quotient in Mathlib's
`Matrix.GeneralLinearGroup.Projective`; no group recognition is used.
-/

public instance Matrix.ProjGenLinGroup.finite
    (ι R : Type*) [Fintype ι] [DecidableEq ι] [CommRing R] [Finite R] :
    Finite (Matrix.ProjGenLinGroup ι R) := by
  unfold Matrix.ProjGenLinGroup
  infer_instance
