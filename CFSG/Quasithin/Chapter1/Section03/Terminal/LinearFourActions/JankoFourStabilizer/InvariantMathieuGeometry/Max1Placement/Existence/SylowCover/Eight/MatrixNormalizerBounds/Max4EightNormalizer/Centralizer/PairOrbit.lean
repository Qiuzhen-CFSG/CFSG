module

public import CFSG.Quasithin.Chapter1.Section03.Terminal.LinearFourActions.JankoFourStabilizer.InvariantMathieuGeometry.Max1Placement.Existence.SylowCover.Eight.MatrixNormalizerBounds.Max4EightNormalizer.Centralizer.PairOrbit.Transport
public import CFSG.Quasithin.Chapter1.Section03.Terminal.LinearFourActions.JankoFourStabilizer.InvariantMathieuGeometry.Max1Placement.Existence.SylowCover.Eight.MatrixNormalizerBounds.Max4EightNormalizer.Centralizer.PairOrbit.Assembly
public import CFSG.Quasithin.Chapter1.Section03.Terminal.LinearFourActions.JankoFourStabilizer.InvariantMathieuGeometry.Max1Placement.Existence.SylowCover.Eight.MatrixNormalizerBounds.Max4EightNormalizer.Centralizer.PairOrbit.WordAction
public import CFSG.Quasithin.Chapter1.Section03.Terminal.LinearFourActions.JankoFourStabilizer.InvariantMathieuGeometry.Max1Placement.Existence.SylowCover.Eight.MatrixNormalizerBounds.Max4EightNormalizer.Centralizer.PairOrbit.FiniteCertificate

/-!
# 5544 distinct conjugate pairs in the original max2 subgroup

The literal source-factor relations are proved in `Transport`. `Assembly`
realizes a checked mask tree by actual left conjugators and transfers its
distinctness using the proved injectivity of the original kernel products.

`WordAction` proves the full thirteen-bit arithmetic sound for these original
words, and `FiniteCertificate` checks a tree of 5544 distinct mask pairs.
Combining them gives `pair_orbit_witness` without any remaining premise.
The witnesses conjugate the literal increasing-bit products 6607 and 3400
inside the original source subgroup.

Source: ATLAS J4G1-max2W1; Kleidman–Wilson (1988), pp.484–510;
Aschbacher–Smith A.3.12, printed pp.47–48.
-/

public section
namespace CFSG.Quasithin.Chapter1.Terminal.LinearFourActions.JankoFourStabilizer.Max1Placement.SylowCover.MatrixNormalizerBounds.Max4EightCentralizer

/-- There are 5544 distinct actual left-conjugate pairs of the two original max2 words. -/
theorem pair_orbit_witness : PairOrbitWitness := by
  obtain ⟨c⟩ := PairOrbitData.orbit_certificate
  exact pair_orbit_witness_of_certificates PairOrbitData.source_action_law c

end CFSG.Quasithin.Chapter1.Terminal.LinearFourActions.JankoFourStabilizer.Max1Placement.SylowCover.MatrixNormalizerBounds.Max4EightCentralizer
