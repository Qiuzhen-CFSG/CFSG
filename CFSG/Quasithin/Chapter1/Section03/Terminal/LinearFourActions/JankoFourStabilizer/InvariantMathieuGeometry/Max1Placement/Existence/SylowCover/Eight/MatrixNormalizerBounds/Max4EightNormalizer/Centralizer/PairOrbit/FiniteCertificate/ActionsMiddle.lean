module

public import CFSG.Quasithin.Chapter1.Section03.Terminal.LinearFourActions.JankoFourStabilizer.InvariantMathieuGeometry.Max1Placement.Existence.SylowCover.Eight.MatrixNormalizerBounds.Max4EightNormalizer.Centralizer.PairOrbit.FiniteCertificate.ActionsFirst

/-!
# Certified scalar actions: indices 512 through 1023

This bounded kernel check extends the already certified prefix. The three
small compilation stages limit simultaneous reduction of the action table.

Source: ATLAS J4G1-max2W1; the retained
NormalClosureControl/Certificates/source/kernel_candidate.json.
-/

public section
namespace CFSG.Quasithin.Chapter1.Terminal.LinearFourActions.JankoFourStabilizer.Max1Placement.SylowCover.MatrixNormalizerBounds.Max4EightCentralizer.PairOrbitData.FiniteTree

theorem scalar_prefix_1024 (i : Nat) (hi : i < 1024) : scalarCheck i = true := by
  have checked : allBlock scalarCheck 9 512 = true := by decide +kernel
  by_cases hprev : i < 512
  · exact scalar_prefix_512 i hprev
  · exact allBlock_spec scalarCheck 9 512 checked i (by omega) (by omega)

end CFSG.Quasithin.Chapter1.Terminal.LinearFourActions.JankoFourStabilizer.Max1Placement.SylowCover.MatrixNormalizerBounds.Max4EightCentralizer.PairOrbitData.FiniteTree
