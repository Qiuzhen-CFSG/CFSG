module

public import CFSG.Quasithin.Chapter1.Section03.Terminal.LinearFourActions.JankoFourStabilizer.InvariantMathieuGeometry.Max1Placement.Existence.SylowCover.Structure.OrderSpectrum.OutsideKernelOrders.AbstractCatalogue.Localization.PointwiseExclusion.GroupTests.Basic

/-!
# Literal conjugate inputs and coordinate comparison

The inputs here are inverse conjugates by the original presentation generators.
Two checked collected products can be compared under the full-order hypothesis;
pairwise commutation makes every polynomial coordinate difference vanish.
Source: Aschbacher–Smith A.3.12, pp.47–48; the literal PC conventions documented
in PointwiseExclusion/source/README.md. These adapters assume the displayed word
identities and do not assert unverified conjugate calculations.
-/

@[expose] public section
namespace CFSG.Quasithin.Chapter1.Terminal.LinearFourActions.JankoFourStabilizer.Max1Placement.SylowCover.OutsideKernelOrders.AbstractCatalogue.Localization.GroupTests
open PointwiseCalculation Symbolic
open Janko4.LocalStructure.SylowNormalEights Presentation Profiles

def conjugateInput : Option (Fin 21) → Word
  | none => inputWord
  | some i => constant (inverseGeneratorWord i) ++ inputWord ++ constant [i]

theorem value_conjugateInput (b : Boolean.Bits) (i : Option (Fin 21)) :
    value (conjugateInput i) (valuation b) = conjugateTest (boolValue b) i := by
  cases i with
  | none => exact value_inputWord b
  | some i =>
    simp only [conjugateInput, value_append, value_constant, value_inputWord,
      wordValue_inverseGeneratorWord, wordValue_cons, wordValue_nil, mul_one, conjugateTest]

/-- Coordinate difference of two actually commuting conjugates. -/
theorem pair_difference (hcard : Nat.card Carrier = 2^21)
    (p q : Fin 21 → Poly) (a c : Option (Fin 21)) (b : Boolean.Bits)
    (hp : value (coordinates p) (valuation b) =
      conjugateTest (boolValue b) a * conjugateTest (boolValue b) c)
    (hq : value (coordinates q) (valuation b) =
      conjugateTest (boolValue b) c * conjugateTest (boolValue b) a)
    (hc : PairwiseConjugateCommutation (boolValue b)) (i : Fin 21) :
    polyValue (add (p i) (q i)) (valuation b) = false := by
  have he : value (coordinates p) (valuation b) = value (coordinates q) (valuation b) :=
    hp.trans ((hc a c).eq.trans hq.symm)
  rw [polyValue_add, coordinates_injective hcard p q (valuation b) he i, Bool.xor_self]

/-- Direct application to collected literal conjugate-input products. -/
theorem pair_difference_of_collection (hcard : Nat.card Carrier = 2^21)
    (p q : Fin 21 → Poly) (a c : Option (Fin 21))
    (hp : ∀ v, value (coordinates p) v = value (conjugateInput a ++ conjugateInput c) v)
    (hq : ∀ v, value (coordinates q) v = value (conjugateInput c ++ conjugateInput a) v)
    (b : Boolean.Bits) (hc : PairwiseConjugateCommutation (boolValue b)) (i : Fin 21) :
    polyValue (add (p i) (q i)) (valuation b) = false := by
  apply pair_difference hcard p q a c b _ _ hc i
  · rw [hp, value_append, value_conjugateInput, value_conjugateInput]
  · rw [hq, value_append, value_conjugateInput, value_conjugateInput]

end CFSG.Quasithin.Chapter1.Terminal.LinearFourActions.JankoFourStabilizer.Max1Placement.SylowCover.OutsideKernelOrders.AbstractCatalogue.Localization.GroupTests
