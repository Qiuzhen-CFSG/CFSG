module

public import Theory.SpecificGroups.Janko4.Model.Cardinality.LocalInvolutionCensus.FiberCensus.Forest.Coverage.MatrixEvaluation.InverseProducts
public import Theory.SpecificGroups.Janko4.Model.Cardinality.LocalInvolutionCensus.FiberCensus.KernelRows
public import Theory.SpecificGroups.Janko4.Model.Cardinality.LocalInvolutionCensus.Fusion.Evaluation
public import Theory.SpecificGroups.Janko4.Model.Cardinality.LocalInvolutionCensus.Fusion.ProductsCase0_4
public import Theory.SpecificGroups.Janko4.Model.Cardinality.LocalInvolutionCensus.Fusion.ProductsCase0_5
public import Theory.SpecificGroups.Janko4.Model.Cardinality.LocalInvolutionCensus.Fusion.ProductsCase0_7
import Mathlib.Tactic.FinCases

/-!
# Matrix evaluations for the max2 square-one exclusion

The four source lifts reuse the existing fusion evaluations. Their certified
squares are the identity, so the same matrices evaluate their inverses. The
thirteen inverse factor witnesses are identified by checked right-inverse
products and cancellation under the source matrix homomorphism.

These are unconditional evaluations of the literal ATLAS `J4G1-max2W1`
words; no subgroup order, quotient coverage or conjugacy assertion is used.
The program is attributed to R. A. Wilson, S. J. Nickerson and J. N. Bray;
see the preserved `TwoCoreCentralizer/source/README.md` and the witness
description in `Coverage/source/README.md`.
-/

public section
namespace Janko4.Cardinality.LocalInvolutionCensus.FiberCensus.Forest.Coverage
open OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData
open LowerBound KernelSeparation
open Janko4.GeneratorCertificates KernelRows
open Janko4.Cardinality.KernelCount.Relations (eval_inv)

/-- The four literal source lifts evaluate to the published matrices. -/
theorem eval_lift (j : Fin 4) :
    sourceMatrix (sourceLift j) = decodeRows (liftRows j) :=
  FusionCertificates.eval_lift j

private theorem lift_mul_self (j : Fin 4) :
    decodeRows (liftRows j) * decodeRows (liftRows j) = 1 := by
  fin_cases j
  · change decodeRows packedOne * decodeRows packedOne = 1
    rw [decode_packedOne, one_mul]
  · change decodeRows w10Rows * decodeRows w10Rows = 1
    rw [← decode_packedMul, FusionCertificates.Case0_4.product_00, decode_packedOne]
  · change decodeRows FusionCertificates.lift2Rows * decodeRows FusionCertificates.lift2Rows = 1
    rw [← decode_packedMul, FusionCertificates.Case0_5.product_00, decode_packedOne]
  · change decodeRows FusionCertificates.lift3Rows * decodeRows FusionCertificates.lift3Rows = 1
    rw [← decode_packedMul, FusionCertificates.Case0_7.product_00, decode_packedOne]

/-- The source lifts and their inverses have the same certified matrices. -/
theorem eval_inverse_lift (j : Fin 4) :
    sourceMatrix ((sourceLift j)⁻¹) = decodeRows (liftRows j) :=
  eval_inv sourceMatrix (eval_lift j) (lift_mul_self j)

/-- The published inverse witnesses evaluate the actual inverse source factors. -/
theorem eval_inverse_factor (i : Fin 13) :
    sourceMatrix ((LowerBound.kernelFactor i)⁻¹) = decodeRows (inverseFactorRows i) :=
  eval_inv sourceMatrix (KernelSeparation.eval_factor i) (by
    rw [← decode_packedMul, MatrixEvaluation.factor_mul_inverse, decode_packedOne])

end Janko4.Cardinality.LocalInvolutionCensus.FiberCensus.Forest.Coverage
