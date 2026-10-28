/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Algebra/IcosianConjugation.lean.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Theory.AtlasPort.Janko2.Algebra.IcosianOrderBasis

/-!
# IcosianConjugation

Quaternion conjugation preserves the integral icosian order. Its formula
in the four basis coefficients has golden-integral entries.

Source: Gerald Höhn, ATLAS, `Atlas/Algebra/IcosianConjugation.lean`, revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted to CFSG Lean 4.33.0; imports and public module boundaries changed.
Definition bodies remain exposed for the coordinate calculations in consumers.
-/

@[expose] public section


set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Atlas.Algebra
open scoped Quaternion QuadraticAlgebra

theorem icosianBasisCoefficients_star (x : IcosianQuaternion) :
    icosianBasisCoefficients (star x)=
      ![icosianBasisCoefficients x 0+icosianBasisCoefficients x 2-
          goldenSigma*icosianBasisCoefficients x 3,
        -icosianBasisCoefficients x 1,-icosianBasisCoefficients x 2,
        -icosianBasisCoefficients x 3] := by
  funext i
  fin_cases i <;> ext <;> simp [icosianBasisCoefficients,goldenSigma,
    goldenTau,QuadraticAlgebra.omega,pow_two] <;> ring

theorem icosianOrder_star_mem {x : IcosianQuaternion} (hx : x ∈ icosianOrder) :
    star x ∈ icosianOrder := by
  have hs : goldenSigma ∈ goldenIntegerToRational.range :=
    ⟨1-QuadraticAlgebra.omega,by ext <;>
      simp [goldenIntegerToRational,goldenSigma,goldenTau,QuadraticAlgebra.omega]⟩
  intro i
  rw [icosianBasisCoefficients_star]
  fin_cases i
  · exact goldenIntegerToRational.range.sub_mem
      (goldenIntegerToRational.range.add_mem (hx 0) (hx 2))
      (goldenIntegerToRational.range.mul_mem hs (hx 3))
  · exact goldenIntegerToRational.range.neg_mem (hx 1)
  · exact goldenIntegerToRational.range.neg_mem (hx 2)
  · exact goldenIntegerToRational.range.neg_mem (hx 3)

end Atlas.Algebra
