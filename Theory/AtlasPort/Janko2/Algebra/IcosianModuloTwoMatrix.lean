/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Algebra/IcosianModuloTwoMatrix.lean.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Theory.AtlasPort.Janko2.Algebra.GoldenModuloTwo
public import Mathlib.Data.Matrix.Basic
public import Mathlib.Algebra.CharP.Two

/-!
# IcosianModuloTwoMatrix

Four coefficients over F₄ identify the reduced icosian algebra with
two-by-two matrices. Explicit inverse formulas and coordinate multiplication
verify the matrix presentation.

Source: Gerald Höhn, ATLAS, `Atlas/Algebra/IcosianModuloTwoMatrix.lean`, revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted to CFSG Lean 4.33.0 with public imports and exposed definition bodies.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false
namespace Atlas.Algebra
open scoped Matrix QuadraticAlgebra

abbrev IcosianMatrix := Matrix (Fin 2) (Fin 2) GoldenFour

def icosianMatrixFromCoefficients (a : Fin 4 → GoldenFour) : IcosianMatrix :=
  !![a 0+a 1+goldenFourTau*a 3, a 1+(goldenFourTau+1)*a 2+goldenFourTau*a 3;
     goldenFourTau*(a 2+a 3), a 0+a 1+a 2+a 3]

def icosianMatrixCoefficients (m : IcosianMatrix) : Fin 4 → GoldenFour :=
  let d := (goldenFourTau+1)*(m 1 1+m 0 0)+goldenFourTau*m 1 0
  let c := (goldenFourTau+1)*(m 1 1+m 0 0)+m 1 0
  let b := m 0 1+(goldenFourTau+1)*c+goldenFourTau*d
  ![m 0 0+b+goldenFourTau*d,b,c,d]

theorem icosianMatrixFromCoefficients_mul (a b : Fin 4 → GoldenFour) :
    icosianMatrixFromCoefficients (icosianCoefficientProduct goldenFourTau a b)=
      icosianMatrixFromCoefficients a*icosianMatrixFromCoefficients b := by
  funext i j
  fin_cases i <;> fin_cases j <;> ext <;>
    simp [icosianMatrixFromCoefficients,icosianCoefficientProduct,Matrix.mul_apply,
      Fin.sum_univ_two,goldenFourTau,QuadraticAlgebra.omega] <;>
    simp only [CharTwo.sub_eq_add] <;> ring_nf <;>
    simp only [(show (2 : ZMod 2) = 0 from rfl), mul_zero, add_zero, (show (4 : ZMod 2) = 0 from rfl),
      (show (3 : ZMod 2) = 1 from rfl), mul_one, (show (6 : ZMod 2) = 0 from rfl),
      (show (5 : ZMod 2) = 1 from rfl), (show (9 : ZMod 2) = 1 from rfl),
      (show (7 : ZMod 2) = 1 from rfl)]

theorem icosianMatrixFromCoefficients_inverse (m : IcosianMatrix) :
    icosianMatrixFromCoefficients (icosianMatrixCoefficients m)=m := by
  funext i j
  fin_cases i <;> fin_cases j <;> ext <;>
    simp [icosianMatrixFromCoefficients,icosianMatrixCoefficients,
      goldenFourTau,QuadraticAlgebra.omega] <;> ring_nf <;>
    simp only [(show (9 : ZMod 2) = 1 from rfl), mul_one, (show (2 : ZMod 2) = 0 from rfl), mul_zero,
      add_zero, (show (8 : ZMod 2) = 0 from rfl), (show (14 : ZMod 2) = 0 from rfl),
      (show (6 : ZMod 2) = 0 from rfl), (show (23 : ZMod 2) = 1 from rfl),
      (show (22 : ZMod 2) = 0 from rfl), (show (12 : ZMod 2) = 0 from rfl),
      (show (10 : ZMod 2) = 0 from rfl), (show (4 : ZMod 2) = 0 from rfl),
      (show (16 : ZMod 2) = 0 from rfl), zero_add, (show (3 : ZMod 2) = 1 from rfl),
      (show (24 : ZMod 2) = 0 from rfl)]

theorem icosianMatrixCoefficients_inverse (a : Fin 4 → GoldenFour) :
    icosianMatrixCoefficients (icosianMatrixFromCoefficients a)=a := by
  funext i
  fin_cases i <;> ext <;>
    simp [icosianMatrixFromCoefficients,icosianMatrixCoefficients,
      goldenFourTau,QuadraticAlgebra.omega] <;> ring_nf <;>
    simp only [(show (9 : ZMod 2) = 1 from rfl), mul_one, (show (10 : ZMod 2) = 0 from rfl), mul_zero,
      add_zero, (show (26 : ZMod 2) = 0 from rfl), (show (8 : ZMod 2) = 0 from rfl),
      (show (14 : ZMod 2) = 0 from rfl), (show (23 : ZMod 2) = 1 from rfl),
      (show (24 : ZMod 2) = 0 from rfl), (show (40 : ZMod 2) = 0 from rfl),
      (show (22 : ZMod 2) = 0 from rfl), (show (7 : ZMod 2) = 1 from rfl),
      (show (6 : ZMod 2) = 0 from rfl), (show (18 : ZMod 2) = 0 from rfl),
      (show (17 : ZMod 2) = 1 from rfl), (show (16 : ZMod 2) = 0 from rfl),
      (show (28 : ZMod 2) = 0 from rfl), (show (2 : ZMod 2) = 0 from rfl), zero_add,
      (show (4 : ZMod 2) = 0 from rfl), (show (3 : ZMod 2) = 1 from rfl)]

end Atlas.Algebra
