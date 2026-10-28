module

public import Theory.SpecificGroups.BabyMonster.Order.LowerBound.ImageSize.RemainingFactors.SevenSquare.Grid
public import Theory.SpecificGroups.BabyMonster.Order.LowerBound.ImageSize.RemainingFactors.LargePrimes.Packed

/-!
# Addition of packed vectors for the seven-square grid

Packed XOR agrees with addition of binary row vectors. This converts the
concrete coordinate separation checks into injectivity of the sums used by
`GridCertificate.ofTwoCycles`.

The row encoding and its soundness are those of `LargePrimes.Packed`, using
the unchanged ATLAS data documented in `LowerBound/source/README.md`.
-/

@[expose] public section

namespace BabyMonster.OrderLowerBound.RemainingFactors.SevenSquare

open LargePrimes

theorem packedVector_xor (x y : ℕ) : vector (x ^^^ y) = vector x + vector y := by
  funext k
  exact bit_xor x y k.val

end BabyMonster.OrderLowerBound.RemainingFactors.SevenSquare
