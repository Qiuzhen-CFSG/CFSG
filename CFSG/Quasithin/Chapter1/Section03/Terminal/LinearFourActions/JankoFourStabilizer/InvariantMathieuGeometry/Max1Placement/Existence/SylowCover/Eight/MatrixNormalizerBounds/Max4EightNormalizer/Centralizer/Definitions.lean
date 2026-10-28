module

public import CFSG.Quasithin.Chapter1.Section03.Terminal.LinearFourActions.JankoFourStabilizer.InvariantMathieuGeometry.Max1Placement.Existence.SylowCover.Eight.MatrixNormalizerBounds.Max4Transport
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.Generation.LowerBound.Source

/-!
# Markings for a finite max4-eight centralizer calculation

The three basis involutions of the literal eight are to be carried to the
original max2 words: mask 6607, the central involution t, and mask 3400.
The conjugator first sends the second basis involution to a, then undoes
the existing max2 bridge. The independent orbit certificate concerns left
conjugation of the two marked words by elements of the original max2 subgroup.

These are shared finite-certificate contracts, not assertions of their truth.
The counting module uses both certificates to bound the full ambient
centralizer. Neither relative centralization nor an abstract local shape
is substituted for that bound.

Source context: ATLAS J4G1-max4W1 and J4G1-max2W1, with original bytes and
attribution retained in NormalEight and TwoCoreCentralizer; Kleidman–Wilson
(1988), pp.484–510; the sporadic-overgroup input to Aschbacher–Smith A.3.12,
printed pp.47–48. The untrusted exploration is retained in source/discover.py.
-/

@[expose] public section
namespace CFSG.Quasithin.Chapter1.Terminal.LinearFourActions.JankoFourStabilizer.Max1Placement.SylowCover.MatrixNormalizerBounds.Max4EightCentralizer
open Subgroup Janko4 Janko4.LocalStructure.SymmetricLinear
open Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData

/-- First marked word in the original max2 normal closure, in increasing-bit order. -/
abbrev sourceP : sourceSubgroup := LowerBound.kernelProduct 6607
/-- Second marked word in the same literal max2 carrier. -/
abbrev sourceQ : sourceSubgroup := LowerBound.kernelProduct 3400

/-- The proposed left conjugator from the max4 eight to the original max2 words. -/
def bridge : Model := h * (((NormalEight.element 2 : max4Subgroup) : Model) * a) ^ 5

/-- Three literal word identities; their finite certificates remain to be supplied. -/
def Marking : Prop :=
  (MulAut.conj bridge) (NormalEight.element 1 : Model) = (sourceP : Model) ∧
  (MulAut.conj bridge) (NormalEight.element 2 : Model) = t ∧
  (MulAut.conj bridge) (NormalEight.element 3 : Model) = (sourceQ : Model)

/-- Left conjugation of the two marked words, inside the actual source subgroup. -/
def pairOrbit (g : sourceSubgroup) : sourceSubgroup × sourceSubgroup :=
  ((MulAut.conj g) sourceP, (MulAut.conj g) sourceQ)

/-- A finite lower bound on this actual pair orbit, without any exhaustiveness premise. -/
def PairOrbitWitness : Prop :=
  ∃ w : Fin 5544 → sourceSubgroup, Function.Injective (fun i => pairOrbit (w i))

end CFSG.Quasithin.Chapter1.Terminal.LinearFourActions.JankoFourStabilizer.Max1Placement.SylowCover.MatrixNormalizerBounds.Max4EightCentralizer
