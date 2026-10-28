module

public import CFSG.Quasithin.Chapter1.Section03.Terminal.LinearFourActions.JankoFourStabilizer.InvariantMathieuGeometry.Max1Placement.Existence.SylowCover.Eight.MatrixNormalizerBounds.Max4EightNormalizer.Centralizer.Counting
public import CFSG.Quasithin.Chapter1.Section03.Terminal.LinearFourActions.JankoFourStabilizer.InvariantMathieuGeometry.Max1Placement.Existence.SylowCover.Eight.MatrixNormalizerBounds.Max4EightNormalizer.Centralizer.Marking
public import CFSG.Quasithin.Chapter1.Section03.Terminal.LinearFourActions.JankoFourStabilizer.InvariantMathieuGeometry.Max1Placement.Existence.SylowCover.Eight.MatrixNormalizerBounds.Max4EightNormalizer.Centralizer.PairOrbit
public import CFSG.Quasithin.Chapter1.Section03.Terminal.LinearFourActions.JankoFourStabilizer.InvariantMathieuGeometry.Max1Placement.Existence.SylowCover.Eight.MatrixNormalizerBounds.Max4EightNormalizer.Action
public import Theory.GroupTheory.NormalizerCentralizerLift

/-!
# Full ambient centralizer containment for the literal max4 eight

The unconditional relative-centralizer lower bound is combined with the
full ambient upper bound obtained from the marking and pair-orbit witnesses.
The actual max4 action realizes every automorphism of the literal eight,
so the normalizer-centralizer lifting theorem gives the normalizer corollary.

The checked literal marking and 5544 distinct conjugate pairs discharge both
finite-certificate premises. Thus the full ambient centralizer lies in max4,
without an ambient order, simplicity, maximality or overgroup-catalogue input.
The parent retains the final normalizer equality and row-two source assembly.

Source context: Kleidman–Wilson (1988), pp.484–510, and the sporadic branch
of Aschbacher–Smith A.3.12, printed pp.47–48.
-/

public section
namespace CFSG.Quasithin.Chapter1.Terminal.LinearFourActions.JankoFourStabilizer.Max1Placement.SylowCover.MatrixNormalizerBounds
open Subgroup Janko4 Janko4.LocalStructure.SymmetricLinear

/-- The two concrete certificates suffice for full ambient centralizer containment. -/
theorem max4_eight_centralizer_le_of_marking_and_pair_orbit
    (hm : Max4EightCentralizer.Marking) (ho : Max4EightCentralizer.PairOrbitWitness) :
    centralizer (max4Eight : Set Model) ≤ max4Subgroup :=
  Max4EightCentralizer.centralizer_le_of_card_le
    (Max4EightCentralizer.centralizer_card_le hm ho)

/-- Actual application to the literal normalizer action, with both certificates explicit. -/
theorem max4_eight_normalizer_le_of_marking_and_pair_orbit
    (hm : Max4EightCentralizer.Marking) (ho : Max4EightCentralizer.PairOrbitWitness) :
    normalizer (max4Eight : Set Model) ≤ max4Subgroup :=
  normalizer_le_of_centralizer_le_of_surjective max4Eight max4Subgroup
    (max4_eight_centralizer_le_of_marking_and_pair_orbit hm ho)
    max4_eight_action_surjective

/-- The full ambient centralizer of the literal max4 eight lies in max4. -/
theorem max4_eight_centralizer_le :
    centralizer (max4Eight : Set Model) ≤ max4Subgroup :=
  max4_eight_centralizer_le_of_marking_and_pair_orbit
    Max4EightCentralizer.marking Max4EightCentralizer.pair_orbit_witness

/-- The full normalizer bound follows from centralizer containment and the actual max4 action. -/
theorem max4_eight_normalizer_le_via_centralizer :
    normalizer (max4Eight : Set Model) ≤ max4Subgroup :=
  normalizer_le_of_centralizer_le_of_surjective max4Eight max4Subgroup
    max4_eight_centralizer_le max4_eight_action_surjective

end CFSG.Quasithin.Chapter1.Terminal.LinearFourActions.JankoFourStabilizer.Max1Placement.SylowCover.MatrixNormalizerBounds
