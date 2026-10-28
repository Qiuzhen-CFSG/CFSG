module

public import CFSG.Quasithin.Chapter1.Section03.Terminal.LinearFourActions.JankoFourStabilizer.InvariantMathieuGeometry.Max1Placement.Existence.SylowCover.Eight.MatrixNormalizerBounds.Max4EightNormalizer.Centralizer.PairOrbit.FiniteCertificate.Checks

/-!
# A checked 5544-node tree of distinct max2 mask pairs

The certificate retains all thirteen bits, starts at `(6607, 3400)`, and
uses earlier parent indices with the literal right-action edges. A checked
recovery function on packed pair keys proves injectivity. Scalar actions are
certified once per mask and reused by the edge checker. No exhaustive orbit
coverage or original-word soundness hypothesis is needed for this finite result.

The existing `Assembly.pair_orbit_witness_of_certificates` consumes this
certificate together with its separate `SourceActionLaw` producer.

Source: retained ATLAS J4G1-max2W1 and kernel_candidate.json, documented by
Centralizer/source; Kleidman–Wilson (1988), pp.484–510, and Aschbacher–Smith
A.3.12, printed pp.47–48.
-/

public section
namespace CFSG.Quasithin.Chapter1.Terminal.LinearFourActions.JankoFourStabilizer.Max1Placement.SylowCover.MatrixNormalizerBounds.Max4EightCentralizer.PairOrbitData

/-- The full finite pair tree, independently of the original-word action law. -/
theorem orbit_certificate : Nonempty OrbitCertificate :=
  FiniteTree.certificate_of_checks FiniteTree.actions_checked FiniteTree.tree_checked

end CFSG.Quasithin.Chapter1.Terminal.LinearFourActions.JankoFourStabilizer.Max1Placement.SylowCover.MatrixNormalizerBounds.Max4EightCentralizer.PairOrbitData
