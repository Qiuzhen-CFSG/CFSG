module

/-
Copyright (c) 2026 Gerald Höhn and the ATLAS contributors. All rights reserved.
Covered by the ATLAS Research and Attribution License 1.0 (LICENSES/ATLAS.txt).
Source: Atlas/Algebra/SplitOctonion/BasisChecks.lean, revision
8eabb35afe2b5e45bf913a2d05c53e558d2e2917; see LICENSES/ATLAS-CITATION.cff.
Changes: CFSG import paths and Lean 4.33 public module boundaries.
-/

public import Theory.AtlasPort.Algebra.SplitOctonion.Basic
public import Mathlib.LinearAlgebra.BilinearMap
public import Mathlib.LinearAlgebra.StdBasis

/-! Bilinearity reduces preservation of octonion multiplication to standard basis pairs. -/

@[expose] public section

namespace Atlas.SplitOctonion
variable {F : Type*} [CommRing F]

/-- Product preservation is determined by the 64 standard basis pairs. -/
theorem map_mul_of_basis (g : Carrier F →ₗ[F] Carrier F)
    (h : ∀ i j, g (mul (basisVector i) (basisVector j)) =
      mul (g (basisVector i)) (g (basisVector j))) :
    ∀ a b, g (mul a b) = mul (g a) (g b) := by
  have he : multiplication.compr₂ g = multiplication.compl₁₂ g g := by
    apply (Pi.basisFun F (Fin 8)).ext
    intro i
    apply (Pi.basisFun F (Fin 8)).ext
    intro j
    simpa [multiplication, Pi.basisFun_apply, basisVector] using h i j
  intro a b
  exact congrArg (fun f : Carrier F →ₗ[F] Carrier F →ₗ[F] Carrier F => f a b) he

/-- Equality of coordinate linear maps is determined by eight images. -/
theorem linearMap_ext (f g : Carrier F →ₗ[F] Carrier F)
    (h : ∀ i, f (basisVector i) = g (basisVector i)) : f = g :=
  (Pi.basisFun F (Fin 8)).ext (fun i => by simpa [Pi.basisFun_apply, basisVector] using h i)
end Atlas.SplitOctonion
