/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Algebra/IcosianReductionConjugation.lean.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Theory.AtlasPort.Janko2.Algebra.IcosianConjugation
public import Theory.AtlasPort.Janko2.Algebra.IcosianModuloTwo
public import Mathlib.LinearAlgebra.Matrix.Adjugate

/-!
# IcosianReductionConjugation

Quaternion conjugation becomes matrix adjugation modulo two.
The conjugation formula in integral coefficients reduces to the explicit
adjugate formula for two-by-two matrices.

Source: Gerald Höhn, ATLAS, `Atlas/Algebra/IcosianReductionConjugation.lean`, revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted to CFSG Lean 4.33.0 with public imports and exposed definition bodies.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Atlas.Algebra
open scoped Matrix QuadraticAlgebra

def icosianOrderStar (x : icosianOrder) : icosianOrder :=
  ⟨star x.val,icosianOrder_star_mem x.property⟩

def icosianCoefficientStar {R : Type*} [CommRing R] (t : R) (a : Fin 4 → R) : Fin 4 → R :=
  ![a 0+a 2-(1-t)*a 3,-a 1,-a 2,-a 3]

theorem icosianIntegralCoefficients_star (x : icosianOrder) :
    icosianIntegralCoefficients (icosianOrderStar x)=
      icosianCoefficientStar QuadraticAlgebra.omega (icosianIntegralCoefficients x) := by
  funext i
  apply goldenIntegerToRational_injective
  rw [icosianIntegralCoefficients_spec]
  change icosianBasisCoefficients (star x.val) i=_
  rw [icosianBasisCoefficients_star]
  have ht : goldenIntegerToRational (QuadraticAlgebra.omega : GoldenInteger)=goldenTau := rfl
  fin_cases i <;> simp [icosianCoefficientStar,ht,goldenSigma,icosianIntegralCoefficients_spec]

theorem icosianMatrixFromCoefficients_star (a : Fin 4 → GoldenFour) :
    icosianMatrixFromCoefficients (icosianCoefficientStar goldenFourTau a)=
      Matrix.adjugate (icosianMatrixFromCoefficients a) := by
  rw [Matrix.adjugate_fin_two]
  funext i j
  fin_cases i <;> fin_cases j <;> ext <;>
    simp [icosianMatrixFromCoefficients,icosianCoefficientStar,
      goldenFourTau,QuadraticAlgebra.omega] <;>
    (try simp only [CharTwo.sub_eq_add]) <;> ring_nf <;>
    simp only [(show (2 : ZMod 2)=0 from rfl),(show (3 : ZMod 2)=1 from rfl),
      mul_zero,mul_one,add_zero]

/-- Quaternion conjugation becomes matrix adjugation under the actual reduction. -/
theorem icosianModuloTwo_star (x : icosianOrder) :
    icosianModuloTwo (icosianOrderStar x)=Matrix.adjugate (icosianModuloTwo x) := by
  change icosianMatrixFromCoefficients (icosianReducedCoefficients _)=
    Matrix.adjugate (icosianMatrixFromCoefficients _)
  rw [← icosianMatrixFromCoefficients_star]
  apply congrArg icosianMatrixFromCoefficients
  funext i
  unfold icosianReducedCoefficients
  rw [icosianIntegralCoefficients_star]
  have ht : goldenModuloTwo (QuadraticAlgebra.omega : GoldenInteger)=goldenFourTau := rfl
  fin_cases i <;> simp [icosianCoefficientStar,ht]

end Atlas.Algebra
