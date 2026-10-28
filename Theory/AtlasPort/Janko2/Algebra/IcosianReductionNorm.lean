/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Algebra/IcosianReductionNorm.lean.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Theory.AtlasPort.Janko2.Algebra.IcosianIntegralNorm
public import Theory.AtlasPort.Janko2.Algebra.IcosianModuloTwo
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-!
# IcosianReductionNorm

Reduced quaternion norm becomes matrix determinant modulo two.
Both operations are the same explicit quadratic polynomial in the four
reduced basis coefficients.

Source: Gerald Höhn, ATLAS, `Atlas/Algebra/IcosianReductionNorm.lean`, revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted to CFSG Lean 4.33.0 with public imports and exposed definition bodies.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Atlas.Algebra
open scoped QuadraticAlgebra Matrix

/-- The full matrix determinant agrees with reduction of the integral reduced norm. -/
theorem icosianMatrixFromCoefficients_det (a : Fin 4 → GoldenFour) :
    Matrix.det (icosianMatrixFromCoefficients a)=icosianCoefficientNorm goldenFourTau a := by
  rw [Matrix.det_fin_two]
  ext <;> simp [icosianMatrixFromCoefficients,icosianCoefficientNorm,
    goldenFourTau,QuadraticAlgebra.omega,pow_two] <;>
    (try simp only [CharTwo.sub_eq_add]) <;> ring_nf <;>
    simp only [(show (2 : ZMod 2)=0 from rfl),(show (3 : ZMod 2)=1 from rfl),
      (show (4 : ZMod 2)=0 from rfl),(show (5 : ZMod 2)=1 from rfl),
      (show (10 : ZMod 2)=0 from rfl),(show (6 : ZMod 2)=0 from rfl),
      mul_zero,mul_one,add_zero,zero_add]

theorem icosianModuloTwo_det (x : icosianOrder) :
    Matrix.det (icosianModuloTwo x)=goldenModuloTwo (icosianIntegralNorm x) := by
  change Matrix.det (icosianMatrixFromCoefficients _)=_
  rw [icosianMatrixFromCoefficients_det]
  have ht : goldenModuloTwo (QuadraticAlgebra.omega : GoldenInteger)=goldenFourTau := rfl
  simp [icosianReducedCoefficients,icosianIntegralNorm,icosianCoefficientNorm,ht]

end Atlas.Algebra
