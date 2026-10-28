module

public import Theory.SpecificGroups.Janko4.Model.Cardinality.LocalInvolutionCensus.FiberCensus.Forest.Coverage.FiniteExclusion.Core
public import Theory.SpecificGroups.Janko4.Model.Cardinality.LocalInvolutionCensus.FiberCensus.Forest.Coverage.FiniteExclusion.Tables.Fiber0

/-!
# Forward row certificates for fiber 0

Untrusted witnesses from the unchanged ATLAS J4G1-max2W1 data of
R. A. Wilson, S. J. Nickerson and J. N. Bray. All uses of these tables
require the kernel certificates. See `Coverage/source/README.md`.
-/

@[expose] public section
namespace Janko4.Cardinality.LocalInvolutionCensus.FiberCensus.Forest.Coverage.FiniteExclusion
open Janko4.GeneratorCertificates
open OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData
open LowerBound KernelSeparation

theorem forward_checked0 (m : Fin 8192) :
    forwardTable0 m.val = KernelSeparation.row m.val := by rfl

theorem forward_semantics0 (m : Fin 8192) :
    unpackRow (forwardTable0 m.val) = unpackRow (forwardRow 0 m) := by
  rw [forward_checked0]
  simp only [forwardRow, unpack_packedRow, liftRows, Matrix.cons_val_zero,
    decode_packedOne, Matrix.vecMul_one]

end Janko4.Cardinality.LocalInvolutionCensus.FiberCensus.Forest.Coverage.FiniteExclusion
