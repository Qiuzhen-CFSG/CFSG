module

public import CFSG.Quasithin.Chapter1.Section03.Terminal.LinearFourActions.JankoFourStabilizer.InvariantMathieuGeometry.Max1Placement.Existence.SylowCover.Eight.MatrixNormalizerBounds.Definitions
public import CFSG.Quasithin.Chapter1.Section03.Terminal.LinearFourActions.JankoFourStabilizer.InvariantMathieuGeometry.Max1Placement.Existence.SylowCover.Eight.MatrixNormalizerBounds.KernelMasks
public import CFSG.Quasithin.Chapter1.Section03.Terminal.LinearFourActions.JankoFourStabilizer.InvariantMathieuGeometry.Max1Placement.Existence.SylowCover.Eight.MatrixNormalizerBounds.Max4Transport
public import CFSG.Quasithin.Chapter1.Section03.Terminal.LinearFourActions.JankoFourStabilizer.InvariantMathieuGeometry.Max1Placement.Existence.SylowCover.Eight.MatrixNormalizerBounds.FirstPureOvergroup
public import CFSG.Quasithin.Chapter1.Section03.Terminal.LinearFourActions.JankoFourStabilizer.InvariantMathieuGeometry.Max1Placement.Existence.SylowCover.Eight.MatrixNormalizerBounds.MixedRow
public import CFSG.Quasithin.Chapter1.Section03.Terminal.LinearFourActions.JankoFourStabilizer.InvariantMathieuGeometry.Max1Placement.Existence.SylowCover.Eight.MatrixNormalizerBounds.ThirdConjugacy
public import CFSG.Quasithin.Chapter1.Section03.Terminal.LinearFourActions.JankoFourStabilizer.InvariantMathieuGeometry.Max1Placement.Existence.SylowCover.Eight.MatrixNormalizerBounds.Max4EightNormalizer

/-!
# Ambient normalizer bounds for the three literal Sylow eights

The first row's full ambient normalizer lies strictly inside its proper
trace-plane stabilizer. The mixed row's normalizer lies strictly inside
proper literal max1. The third row is explicitly conjugate to the certified
max4 eight, whose full normalizer is literal max4. These give the required
alternative unconditionally for each of the three specified matrix subgroups.

The consumer adapter supplies `SylowEightNormalizerRows` from explicit
coverage by these exact subgroups. Coverage and its final application to
normal-eight recognition remain with the catalogue and recognition owners;
no exhaustive catalogue or centralizer profile is assumed in the three bounds.

Source context: Aschbacher–Smith A.3.12, printed pp.47–48, and
Kleidman–Wilson (1988), pp.484–510. Literal subgroup provenance remains in
the imported model modules.
-/

public section
namespace CFSG.Quasithin.Chapter1.Terminal.LinearFourActions.JankoFourStabilizer.Max1Placement.SylowCover.MatrixNormalizerBounds

/-- The third row's full ambient normalizer lies in the actual conjugate of max4. -/
theorem row_two : EightNormalizerAlternative (U 2) :=
  row_two_of_max4_eight_normalizer max4_eight_normalizer_le

/-- All three prescribed literal matrix subgroups have the required full ambient bound. -/
theorem eightNormalizerAlternative (i : Fin 3) : EightNormalizerAlternative (U i) := by
  fin_cases i
  · exact row_zero
  · exact row_one
  · exact row_two

/-- Exact literal coverage discharges the existing normalizer-row contract.
The profile premise is unnecessary for this application. -/
theorem sylowEightNormalizerRows_of_coverage (hcover : Coverage) :
    SylowEightNormalizerRows :=
  normalizerRows_of_coverage hcover eightNormalizerAlternative

end CFSG.Quasithin.Chapter1.Terminal.LinearFourActions.JankoFourStabilizer.Max1Placement.SylowCover.MatrixNormalizerBounds
