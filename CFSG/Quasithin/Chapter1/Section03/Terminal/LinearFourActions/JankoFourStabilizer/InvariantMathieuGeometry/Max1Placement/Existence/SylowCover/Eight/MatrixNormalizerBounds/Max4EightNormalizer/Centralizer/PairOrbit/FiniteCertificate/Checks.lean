module

public import CFSG.Quasithin.Chapter1.Section03.Terminal.LinearFourActions.JankoFourStabilizer.InvariantMathieuGeometry.Max1Placement.Existence.SylowCover.Eight.MatrixNormalizerBounds.Max4EightNormalizer.Centralizer.PairOrbit.FiniteCertificate.ActionsLast

/-!
# Certified bounds, recovery and edges for all 5544 rows

The scalar actions have already been checked against the literal arithmetic.
This final Boolean check verifies recovery indices, all parent bounds, strict
decrease and both transitions at every nonroot row.

Source: ATLAS J4G1-max2W1; the retained
NormalClosureControl/Certificates/source/kernel_candidate.json.
-/

public section
namespace CFSG.Quasithin.Chapter1.Terminal.LinearFourActions.JankoFourStabilizer.Max1Placement.SylowCover.MatrixNormalizerBounds.Max4EightCentralizer.PairOrbitData.FiniteTree

theorem tree_checked (i : Nat) (hi : i < 5544) : rowCheck i = true := by
  have checked : allBlock (fun n => if n < 5544 then rowCheck n else true) 13 0 = true := by
    decide +kernel
  have h := allBlock_spec _ 13 0 checked i (by omega) (by omega)
  simpa only [if_pos hi] using h

end CFSG.Quasithin.Chapter1.Terminal.LinearFourActions.JankoFourStabilizer.Max1Placement.SylowCover.MatrixNormalizerBounds.Max4EightCentralizer.PairOrbitData.FiniteTree
