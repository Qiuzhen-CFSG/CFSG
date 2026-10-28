module

public import CFSG.Quasithin.Chapter1.Section03.Terminal.LinearFourActions.JankoFourStabilizer.InvariantMathieuGeometry.Max1Placement.Existence.SylowCover.Eight.MatrixNormalizerBounds.Max4EightNormalizer.Centralizer.PairOrbit.FiniteCertificate.Checker

/-!
# Certified scalar actions: indices 0 through 511

This bounded kernel check extends the already certified prefix. The three
small compilation stages limit simultaneous reduction of the action table.

Source: ATLAS J4G1-max2W1; the retained
NormalClosureControl/Certificates/source/kernel_candidate.json.
-/

public section
namespace CFSG.Quasithin.Chapter1.Terminal.LinearFourActions.JankoFourStabilizer.Max1Placement.SylowCover.MatrixNormalizerBounds.Max4EightCentralizer.PairOrbitData.FiniteTree

theorem scalar_prefix_512 (i : Nat) (hi : i < 512) : scalarCheck i = true := by
  have checked : allBlock scalarCheck 9 0 = true := by decide +kernel
  exact allBlock_spec scalarCheck 9 0 checked i (by omega) (by omega)

end CFSG.Quasithin.Chapter1.Terminal.LinearFourActions.JankoFourStabilizer.Max1Placement.SylowCover.MatrixNormalizerBounds.Max4EightCentralizer.PairOrbitData.FiniteTree
