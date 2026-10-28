module

public import CFSG.Quasithin.Chapter1.Section03.Terminal.LinearFourActions.JankoFourStabilizer.InvariantMathieuGeometry.Max1Placement.Existence.SylowCover.Eight.MatrixNormalizerBounds.Max4Transport
public import CFSG.Quasithin.Chapter1.Section03.Terminal.LinearFourActions.JankoFourStabilizer.InvariantMathieuGeometry.Max1Placement.Existence.SylowCover.Eight.MatrixNormalizerBounds.Max4EightNormalizer.Action
public import CFSG.Quasithin.Chapter1.Section03.Terminal.LinearFourActions.JankoFourStabilizer.InvariantMathieuGeometry.Max1Placement.Existence.SylowCover.Eight.MatrixNormalizerBounds.Max4EightNormalizer.Centralizer
public import Theory.GroupTheory.NormalizerCentralizerLift

/-!
# The full ambient normalizer of the literal max4 eight

The actual max4 generators realize every automorphism of the embedded normal
eight. An arbitrary ambient normalizer element can therefore be corrected by
an element of max4 to centralize the eight pointwise. The full ambient
centralizer lies in max4 by the checked marking and pair-orbit calculation.
Thus the full normalizer lies in max4, and normality inside max4 supplies the
reverse inclusion. No maximality or ambient simplicity hypothesis is needed.

The conditional reduction interfaces are retained. The final theorem applies
the unconditional bound to `Max4Transport.row_two_of_max4_eight_conjugacy`,
discharging its normalizer premise. The independent conjugacy premise remains
explicit; its producer is `ThirdConjugacy.max4Eight_conjugacy`.

Source context: Kleidman–Wilson (1988), pp.484–510, and Aschbacher–Smith A.3.12.
The actual words and action certificates retain the ATLAS attribution in
`Max4.NormalEight` and the imported action module.
-/

public section
namespace CFSG.Quasithin.Chapter1.Terminal.LinearFourActions.JankoFourStabilizer.Max1Placement.SylowCover.MatrixNormalizerBounds
open Subgroup Janko4 Janko4.LocalStructure.SymmetricLinear

/-- Full-centralizer containment suffices because max4 realizes every action on the eight. -/
theorem max4_eight_normalizer_le_of_centralizer_le
    (hC : centralizer (max4Eight : Set Model) ≤ max4Subgroup) :
    normalizer (max4Eight : Set Model) ≤ max4Subgroup :=
  normalizer_le_of_centralizer_le_of_surjective max4Eight max4Subgroup hC
    max4_eight_action_surjective

/-- With the full-centralizer bound, the literal subgroup is exactly the full normalizer. -/
theorem max4_eight_normalizer_eq_of_centralizer_le
    (hC : centralizer (max4Eight : Set Model) ≤ max4Subgroup) :
    normalizer (max4Eight : Set Model) = max4Subgroup :=
  le_antisymm (max4_eight_normalizer_le_of_centralizer_le hC) max4_le_eight_normalizer

/-- The full ambient normalizer of the literal max4 eight is contained in max4. -/
theorem max4_eight_normalizer_le :
    normalizer (max4Eight : Set Model) ≤ max4Subgroup :=
  max4_eight_normalizer_le_of_centralizer_le max4_eight_centralizer_le

/-- Literal max4 is exactly the full ambient normalizer of its certified eight. -/
theorem max4_eight_normalizer_eq :
    normalizer (max4Eight : Set Model) = max4Subgroup :=
  le_antisymm max4_eight_normalizer_le max4_le_eight_normalizer

/-- The conditional row-two interface with its conjugacy and centralizer premises explicit. -/
theorem row_two_of_max4_eight_centralizer_le
    (hconj : ∃ k : Model, max4Eight.map (MulAut.conj k).toMonoidHom = U 2)
    (hC : centralizer (max4Eight : Set Model) ≤ max4Subgroup) :
    EightNormalizerAlternative (U 2) :=
  row_two_of_max4_eight_conjugacy hconj (max4_eight_normalizer_le_of_centralizer_le hC)

/-- Discharge the literal row-two normalizer premise, retaining only its independent conjugacy. -/
theorem row_two_normalizer_alternative_of_max4_eight_conjugacy
    (hconj : ∃ k : Model, max4Eight.map (MulAut.conj k).toMonoidHom = U 2) :
    EightNormalizerAlternative (U 2) :=
  row_two_of_max4_eight_conjugacy hconj max4_eight_normalizer_le

end CFSG.Quasithin.Chapter1.Terminal.LinearFourActions.JankoFourStabilizer.Max1Placement.SylowCover.MatrixNormalizerBounds
