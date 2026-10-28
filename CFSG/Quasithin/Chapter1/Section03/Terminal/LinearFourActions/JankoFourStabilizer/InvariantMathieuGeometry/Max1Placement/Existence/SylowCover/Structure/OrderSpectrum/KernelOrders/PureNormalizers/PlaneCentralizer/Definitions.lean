module

public import CFSG.Quasithin.Chapter1.Section03.Terminal.LinearFourActions.JankoFourStabilizer.InvariantMathieuGeometry.Max1Placement.Existence.SylowCover.Eight.MatrixNormalizerBounds.Max4EightNormalizer.Centralizer.Definitions

/-!
# The single-orbit input for the max4 plane centralizer

This contract asks for 1386 distinct actual conjugates of the literal source
word with mask 6607. Their disjoint centralizer translates supply the ambient
upper bound in `UpperBound`. The retained discovery tree uses right conjugation;
witnesses for this left-conjugation contract must invert the tree words.

Source context: Aschbacher--Smith A.3.12, pp.47--48, and the original ATLAS
max2 program, with provenance retained in `TwoCoreCentralizer`.
-/

@[expose] public section
namespace CFSG.Quasithin.Chapter1.Terminal.LinearFourActions.JankoFourStabilizer.Max1Placement.SylowCover.KernelOrders.PureNormalizers.PlaneCentralizer
open Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData
open CFSG.Quasithin.Chapter1.Terminal.LinearFourActions.JankoFourStabilizer.Max1Placement.SylowCover.MatrixNormalizerBounds.Max4EightCentralizer

/-- Distinct actual left conjugates of the original max2 word with mask 6607.
There is no claim that these witnesses exhaust its orbit. -/
def SingleOrbitWitness : Prop :=
  ∃ w : Fin 1386 → sourceSubgroup,
    Function.Injective (fun i => (MulAut.conj (w i)) sourceP)

end CFSG.Quasithin.Chapter1.Terminal.LinearFourActions.JankoFourStabilizer.Max1Placement.SylowCover.KernelOrders.PureNormalizers.PlaneCentralizer
