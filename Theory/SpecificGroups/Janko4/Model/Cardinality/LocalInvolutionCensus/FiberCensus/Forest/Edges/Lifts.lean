module

public import Theory.SpecificGroups.Janko4.Model.Cardinality.LocalInvolutionCensus.FiberCensus.Forest.Edges.PackedData
public import Theory.SpecificGroups.Janko4.Model.Cardinality.LocalInvolutionCensus.Fusion.Evaluation

/-!
# Reuse of the certified four source lifts

The fusion certificates already evaluate the same literal source lifts. A
kernel-checked comparison identifies their packed witnesses with those used by
the forest. No rank, fusion conclusion, or group-order assertion is needed.
ATLAS provenance is recorded in `Edges/source/README.md` and `Fusion/source/`.
-/

@[expose] public section
namespace Janko4.Cardinality.LocalInvolutionCensus.FiberCensus.Forest.Edges
open OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData
open LowerBound Janko4.GeneratorCertificates KernelRows
set_option maxRecDepth 10000

theorem liftRows_spec (j : Fin 4) :
    sourceMatrix (sourceLift j) = decodeRows (liftRows j) := by
  have hr : ∀ j : Fin 4,
      liftRows j = ![packedOne, w10Rows, FusionCertificates.lift2Rows, FusionCertificates.lift3Rows] j := by
    intro j
    fin_cases j
    · rfl
    · rfl
    · apply Vector.ext
      intro i hi
      exact (show ∀ i : Fin 112, liftRows2.get i = FusionCertificates.lift2Rows.get i
        from by decide +kernel) ⟨i, hi⟩
    · apply Vector.ext
      intro i hi
      exact (show ∀ i : Fin 112, liftRows3.get i = FusionCertificates.lift3Rows.get i
        from by decide +kernel) ⟨i, hi⟩
  exact (FusionCertificates.eval_lift j).trans (congrArg decodeRows (hr j).symm)
end Janko4.Cardinality.LocalInvolutionCensus.FiberCensus.Forest.Edges
