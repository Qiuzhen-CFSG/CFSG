/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Algebra/IcosianIntegralMultiplication.lean.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Theory.AtlasPort.Janko2.Algebra.IcosianIntegralCoordinates

/-!
# IcosianIntegralMultiplication

Integral icosian coefficients obey the same four-coordinate product
formula as rational coefficients. Injectivity of the golden-integer embedding
transfers the rational multiplication identity.

Source: Gerald Höhn, ATLAS, `Atlas/Algebra/IcosianIntegralMultiplication.lean`, revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted to CFSG Lean 4.33.0; imports and public module boundaries changed.
Definition bodies remain exposed for the coordinate calculations in consumers.
-/

@[expose] public section


set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Atlas.Algebra
open scoped QuadraticAlgebra Quaternion
attribute [local irreducible] icosianBasisCoefficients goldenIntegerToRational

theorem icosianIntegralCoefficients_mul (x y : icosianOrder) :
    icosianIntegralCoefficients (x*y)=icosianCoefficientProduct
      (QuadraticAlgebra.omega : GoldenInteger)
      (icosianIntegralCoefficients x) (icosianIntegralCoefficients y) := by
  funext i
  apply goldenIntegerToRational_injective
  rw [icosianIntegralCoefficients_spec]
  change icosianBasisCoefficients (x.val*y.val) i=_
  rw [icosianBasisCoefficients_mul]
  have ht : goldenIntegerToRational (QuadraticAlgebra.omega : GoldenInteger)=goldenTau := by unfold goldenIntegerToRational goldenTau; rfl
  fin_cases i <;> simp [icosianCoefficientProduct,ht,icosianIntegralCoefficients_spec]

theorem icosianIntegralCoefficients_one :
    icosianIntegralCoefficients (1 : icosianOrder)=![1,0,0,0] := by
  funext i
  apply goldenIntegerToRational_injective
  rw [icosianIntegralCoefficients_spec]
  change icosianBasisCoefficients (1 : IcosianQuaternion) i=_
  fin_cases i <;> simp [icosianBasisCoefficients]

end Atlas.Algebra
