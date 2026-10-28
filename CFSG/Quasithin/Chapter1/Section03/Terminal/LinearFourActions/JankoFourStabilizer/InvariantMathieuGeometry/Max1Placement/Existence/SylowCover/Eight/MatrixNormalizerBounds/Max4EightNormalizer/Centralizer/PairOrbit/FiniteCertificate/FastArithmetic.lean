module

public import CFSG.Quasithin.Chapter1.Section03.Terminal.LinearFourActions.JankoFourStabilizer.InvariantMathieuGeometry.Max1Placement.Existence.SylowCover.Eight.MatrixNormalizerBounds.Max4EightNormalizer.Centralizer.PairOrbit.Arithmetic

/-!
# Simplifying the thirteen-bit arithmetic used by the pair tree

The lower triangle of the certified commutator form gives a small Boolean
formula for the central correction. Symbolic simplification proves equality
with the literal `correction`; the fold and its generator convention are
unchanged. This avoids repeatedly reducing the 13-by-13 table at every edge.

Source: ATLAS J4G1-max2W1 and the retained
NormalClosureControl/Certificates/source/kernel_candidate.json.
-/

@[expose] public section
namespace CFSG.Quasithin.Chapter1.Terminal.LinearFourActions.JankoFourStabilizer.Max1Placement.SylowCover.MatrixNormalizerBounds.Max4EightCentralizer.PairOrbitData.FiniteTree
open Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.NormalClosureControl.IntrinsicCenter

def fastCorrection (a b : Nat) : Bool := ((a.testBit 1 && (b.testBit 1 ^^ false)) ^^
    ((a.testBit 2 && (b.testBit 2 ^^ false)) ^^
    ((a.testBit 3 && (b.testBit 3 ^^ false)) ^^
    ((a.testBit 4 && (b.testBit 4 ^^ (b.testBit 3 ^^ false))) ^^
    ((a.testBit 5 && (b.testBit 5 ^^ (b.testBit 1 ^^ (b.testBit 4 ^^ false)))) ^^
    ((a.testBit 6 && (b.testBit 6 ^^ (b.testBit 1 ^^ (b.testBit 3 ^^ (b.testBit 5 ^^ false))))) ^^
    ((a.testBit 7 && (b.testBit 7 ^^ (b.testBit 2 ^^ (b.testBit 4 ^^ (b.testBit 5 ^^ false))))) ^^
    ((a.testBit 8 && (b.testBit 8 ^^ (b.testBit 1 ^^ (b.testBit 2 ^^ (b.testBit 6 ^^ (b.testBit 7 ^^ false)))))) ^^
    ((a.testBit 9 && (b.testBit 9 ^^ (b.testBit 2 ^^ (b.testBit 3 ^^ (b.testBit 6 ^^ (b.testBit 7 ^^ false)))))) ^^
    ((a.testBit 10 && (b.testBit 10 ^^ (b.testBit 1 ^^ (b.testBit 2 ^^ (b.testBit 5 ^^ (b.testBit 8 ^^ (b.testBit 9 ^^ false))))))) ^^
    ((a.testBit 11 && (b.testBit 11 ^^ (b.testBit 2 ^^ (b.testBit 3 ^^ (b.testBit 4 ^^ (b.testBit 6 ^^ (b.testBit 8 ^^ (b.testBit 10 ^^ false)))))))) ^^
    ((a.testBit 12 && (b.testBit 12 ^^ (b.testBit 1 ^^ (b.testBit 3 ^^ (b.testBit 4 ^^ (b.testBit 8 ^^ (b.testBit 10 ^^ false))))))) ^^ false))))))))))))

theorem correction_fast (a b : Nat) : correction a b = fastCorrection a b := by
  simp [correction, fastCorrection, List.ofFn_succ, commutatorForm]

def fastMultiply (a b : Nat) : Nat := (a ^^^ b) ^^^ (fastCorrection a b).toNat

def fastAction (useY : Bool) (m : Nat) : Nat :=
  (List.finRange 13).foldl (fun r i =>
    if m.testBit i.val then
      fastMultiply r (if useY then
        Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.NormalClosureControl.Certificates.yMasks i
      else Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.NormalClosureControl.Certificates.xMasks i)
    else r) 0

theorem action_fast (s : Bool) (m : Nat) : maskAction s m = fastAction s m := by
  simp only [maskAction, fastAction, maskMultiply, fastMultiply, correction_fast]


end CFSG.Quasithin.Chapter1.Terminal.LinearFourActions.JankoFourStabilizer.Max1Placement.SylowCover.MatrixNormalizerBounds.Max4EightCentralizer.PairOrbitData.FiniteTree
