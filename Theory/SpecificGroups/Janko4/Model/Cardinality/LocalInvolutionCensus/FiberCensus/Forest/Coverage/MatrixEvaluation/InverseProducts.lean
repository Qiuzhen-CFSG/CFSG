module

public import Theory.SpecificGroups.Janko4.Model.Cardinality.LocalInvolutionCensus.FiberCensus.Forest.Coverage.Data
import Mathlib.Tactic.FinCases

/-!
# Checked inverse products for the thirteen max2 factors

Each proposed inverse from `Coverage.Data` is checked against the corresponding
forward factor by packed binary multiplication. The row equalities are proved
by Lean kernel reduction, so the inverse witnesses carry no assumed evaluation.

The factors come from the unchanged ATLAS `J4G1-max2W1` program, by
R. A. Wilson, S. J. Nickerson and J. N. Bray. Source data and attribution remain
in `TwoCoreCentralizer/source/README.md`; the inverse witness generator is
documented in `Coverage/source/README.md`.
-/

public section
namespace Janko4.Cardinality.LocalInvolutionCensus.FiberCensus.Forest.Coverage.MatrixEvaluation
open OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.LowerBound.KernelSeparation
open Janko4.GeneratorCertificates

set_option maxRecDepth 10000
set_option maxHeartbeats 800000

private theorem product_0 :
    packedMul (factorRows 0) (inverseFactorRows 0) = packedOne :=
  packedMul_eq_of_rows _ _ _ (by
    simp only [packedRow, factorRows, inverseFactorRows, packedOne, get_ofFn]
    decide +kernel)

private theorem product_1 :
    packedMul (factorRows 1) (inverseFactorRows 1) = packedOne :=
  packedMul_eq_of_rows _ _ _ (by
    simp only [packedRow, factorRows, inverseFactorRows, packedOne, get_ofFn]
    decide +kernel)

private theorem product_2 :
    packedMul (factorRows 2) (inverseFactorRows 2) = packedOne :=
  packedMul_eq_of_rows _ _ _ (by
    simp only [packedRow, factorRows, inverseFactorRows, packedOne, get_ofFn]
    decide +kernel)

private theorem product_3 :
    packedMul (factorRows 3) (inverseFactorRows 3) = packedOne :=
  packedMul_eq_of_rows _ _ _ (by
    simp only [packedRow, factorRows, inverseFactorRows, packedOne, get_ofFn]
    decide +kernel)

private theorem product_4 :
    packedMul (factorRows 4) (inverseFactorRows 4) = packedOne :=
  packedMul_eq_of_rows _ _ _ (by
    simp only [packedRow, factorRows, inverseFactorRows, packedOne, get_ofFn]
    decide +kernel)

private theorem product_5 :
    packedMul (factorRows 5) (inverseFactorRows 5) = packedOne :=
  packedMul_eq_of_rows _ _ _ (by
    simp only [packedRow, factorRows, inverseFactorRows, packedOne, get_ofFn]
    decide +kernel)

private theorem product_6 :
    packedMul (factorRows 6) (inverseFactorRows 6) = packedOne :=
  packedMul_eq_of_rows _ _ _ (by
    simp only [packedRow, factorRows, inverseFactorRows, packedOne, get_ofFn]
    decide +kernel)

private theorem product_7 :
    packedMul (factorRows 7) (inverseFactorRows 7) = packedOne :=
  packedMul_eq_of_rows _ _ _ (by
    simp only [packedRow, factorRows, inverseFactorRows, packedOne, get_ofFn]
    decide +kernel)

private theorem product_8 :
    packedMul (factorRows 8) (inverseFactorRows 8) = packedOne :=
  packedMul_eq_of_rows _ _ _ (by
    simp only [packedRow, factorRows, inverseFactorRows, packedOne, get_ofFn]
    decide +kernel)

private theorem product_9 :
    packedMul (factorRows 9) (inverseFactorRows 9) = packedOne :=
  packedMul_eq_of_rows _ _ _ (by
    simp only [packedRow, factorRows, inverseFactorRows, packedOne, get_ofFn]
    decide +kernel)

private theorem product_10 :
    packedMul (factorRows 10) (inverseFactorRows 10) = packedOne :=
  packedMul_eq_of_rows _ _ _ (by
    simp only [packedRow, factorRows, inverseFactorRows, packedOne, get_ofFn]
    decide +kernel)

private theorem product_11 :
    packedMul (factorRows 11) (inverseFactorRows 11) = packedOne :=
  packedMul_eq_of_rows _ _ _ (by
    simp only [packedRow, factorRows, inverseFactorRows, packedOne, get_ofFn]
    decide +kernel)

private theorem product_12 :
    packedMul (factorRows 12) (inverseFactorRows 12) = packedOne :=
  packedMul_eq_of_rows _ _ _ (by
    simp only [packedRow, factorRows, inverseFactorRows, packedOne, get_ofFn]
    decide +kernel)

/-- Every published inverse factor is a right inverse of its forward matrix. -/
theorem factor_mul_inverse (i : Fin 13) :
    packedMul (factorRows i) (inverseFactorRows i) = packedOne := by
  fin_cases i
  · exact product_0
  · exact product_1
  · exact product_2
  · exact product_3
  · exact product_4
  · exact product_5
  · exact product_6
  · exact product_7
  · exact product_8
  · exact product_9
  · exact product_10
  · exact product_11
  · exact product_12

end Janko4.Cardinality.LocalInvolutionCensus.FiberCensus.Forest.Coverage.MatrixEvaluation
