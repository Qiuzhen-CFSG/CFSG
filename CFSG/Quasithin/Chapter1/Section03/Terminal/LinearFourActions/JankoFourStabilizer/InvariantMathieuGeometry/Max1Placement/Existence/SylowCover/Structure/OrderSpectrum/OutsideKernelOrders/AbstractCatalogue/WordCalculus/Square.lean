module

public import CFSG.Quasithin.Chapter1.Section03.Terminal.LinearFourActions.JankoFourStabilizer.InvariantMathieuGeometry.Max1Placement.Existence.SylowCover.Structure.OrderSpectrum.OutsideKernelOrders.AbstractCatalogue.WordCalculus.Basic

/-!
# Detecting the two square coordinates

A slice square collects to g19^(a*c) * g20^((b*e+c*d) mod 2).
The 64 short certificates use at most 36 adjacent presentation rewrites.
The order-2^21 hypothesis makes the existing ascending normal forms unique,
so a square equal to one has both displayed coordinates zero.

This is the only part of `WordCalculus` that needs the order premise.
Source context: Aschbacher–Smith A.3.12, pp.47–48; the literal relations
in `SylowNormalEights/PresentationData.lean` and the normal-form theorem
in `SylowNormalEights/Catalogue.lean`.
-/

@[expose] public section

namespace CFSG.Quasithin.Chapter1.Terminal.LinearFourActions.JankoFourStabilizer.Max1Placement.SylowCover.OutsideKernelOrders.AbstractCatalogue.WordProof
open Janko4.LocalStructure.SylowNormalEights Presentation Profiles

def squareMask (n : Code) : Fin (2 ^ 21) :=
  ⟨(524288 * (bit n 0 * bit n 2) +
    1048576 * ((bit n 1 * bit n 4 + bit n 2 * bit n 3) % 2)) % (2 ^ 21),
    Nat.mod_lt _ (by decide)⟩

private theorem square_collection : ∀ n : Code,
    collect 36 (sliceWord n ++ sliceWord n) = maskWord (squareMask n) := by
  decide +kernel

theorem slice_square (n : Code) : sliceValue n ^ 2 = normalForm (squareMask n) := by
  change wordValue (sliceWord n) ^ 2 = normalForm (squareMask n)
  rw [pow_two, ← wordValue_append, ← wordValue_maskWord]
  exact wordValue_eq_of_collect 36 _ _ (square_collection n)

theorem square_zero_of_card (hcard : Nat.card Carrier = 2 ^ 21)
    (n : Code) (hn : sliceValue n ^ 2 = 1) : squareZero n := by
  have h0 : normalForm 0 = 1 := (wordValue_maskWord 0).symm
  have he : squareMask n = 0 :=
    (normalForm_bijective_of_card hcard).injective ((slice_square n).symm.trans (hn.trans h0.symm))
  exact (by decide +kernel : ∀ n : Code, squareMask n = 0 → squareZero n) n he

end CFSG.Quasithin.Chapter1.Terminal.LinearFourActions.JankoFourStabilizer.Max1Placement.SylowCover.OutsideKernelOrders.AbstractCatalogue.WordProof
