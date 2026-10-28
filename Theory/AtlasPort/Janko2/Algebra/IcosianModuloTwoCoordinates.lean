/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Algebra/IcosianModuloTwoCoordinates.lean.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Theory.AtlasPort.Janko2.Algebra.IcosianModuloTwo

/-!
# IcosianModuloTwoCoordinates

The reduction map can be evaluated from any verified integral coefficient
tuple. Uniqueness of integral coefficients makes this interface independent
of the classical choices in coefficient extraction.

Source: Gerald Höhn, ATLAS, `Atlas/Algebra/IcosianModuloTwoCoordinates.lean`, revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted to CFSG Lean 4.33.0 with public imports and exposed definition bodies.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Atlas.Algebra
open scoped Matrix QuadraticAlgebra
attribute [local irreducible] icosianIntegralCoefficients goldenModuloTwo

theorem icosianModuloTwo_synthesis (a : Fin 4 → GoldenInteger) :
    icosianModuloTwo (icosianIntegralSynthesis a)=
      icosianMatrixFromCoefficients (fun i => goldenModuloTwo (a i)) := by
  have he : icosianIntegralCoefficients (icosianIntegralSynthesis a)=a :=
    icosianIntegralEquiv.apply_symm_apply a
  change icosianMatrixFromCoefficients (icosianReducedCoefficients _)=_
  apply congrArg icosianMatrixFromCoefficients
  funext i
  change goldenModuloTwo (icosianIntegralCoefficients _ i)=_
  rw [he]

/-- Computational interface using any verified integral coefficient tuple. -/
theorem icosianModuloTwo_of_coefficients (x : icosianOrder) (a : Fin 4 → GoldenInteger)
    (ha : ∀ i,goldenIntegerToRational (a i)=icosianBasisCoefficients x.val i) :
    icosianModuloTwo x=icosianMatrixFromCoefficients (fun i => goldenModuloTwo (a i)) := by
  have he : icosianIntegralCoefficients x=a := by
    funext i
    apply goldenIntegerToRational_injective
    rw [icosianIntegralCoefficients_spec,ha]
  change icosianMatrixFromCoefficients (icosianReducedCoefficients x)=_
  apply congrArg icosianMatrixFromCoefficients
  funext i
  change goldenModuloTwo (icosianIntegralCoefficients _ i)=_
  rw [he]

end Atlas.Algebra
