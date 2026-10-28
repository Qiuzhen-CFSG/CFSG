module

public import Theory.LinearAlgebra.QuadraticForm.CartanDieudonneCore

/-!
# Cartan--Dieudonne factorization and determinant parity

This module assembles the reusable Cartan--Dieudonne API for a finite-dimensional
nondegenerate quadratic form over a field in which `2` is invertible.  The
reflection construction and its exact action, preservation, and determinant
formulas are provided by `Reflection`; the Wall residual-form reduction in
`CartanDieudonneCore` proves that every quadratic isometry is an ordered
product of anisotropic reflections, with at most `Module.finrank k V`
factors.  The proof is the classical Cartan--Dieudonne argument in Wall's
formulation: nonalternating residual forms lower the moved-space rank by one,
while the alternating (totally isotropic) case uses Wall's exceptional
rank-raising adjustment and the ambient isotropic-dimension bound.

The determinant formula for a reflection is `-1`, so the determinant-one
subgroup admits an even-length factorization.  This result is independent of
the numbered algebraic-group developments and is intended as the shared
linear-algebra implementation for special-orthogonal and Clifford/Spin
consumers.
-/

open Module

namespace QuadraticForm

variable {k V : Type*} [Field k] [Invertible (2 : k)]
variable [AddCommGroup V] [Module k V] [FiniteDimensional k V]

/-- A determinant-one quadratic isometry admits an even Cartan--Dieudonne factorization. -/
public theorem cartanDieudonne_det_one
    (Q : QuadraticForm k V) (hQ : Q.Nondegenerate)
    (g : V ≃ₗ[k] V) (hg : ∀ x, Q (g x) = Q x)
    (hdet : LinearEquiv.det g = 1) :
    ∃ vs : List {v : V // Q v ≠ 0},
      vs.length ≤ finrank k V ∧ Even vs.length ∧
        g = anisotropicReflectionsProduct Q vs := by
  obtain ⟨vs, hlen, hfac⟩ := cartanDieudonne Q hQ g hg
  refine ⟨vs, hlen, ?_, hfac⟩
  apply even_length_of_anisotropicReflectionsProduct_det_eq_one Q vs
  rw [← hfac, hdet]

end QuadraticForm
