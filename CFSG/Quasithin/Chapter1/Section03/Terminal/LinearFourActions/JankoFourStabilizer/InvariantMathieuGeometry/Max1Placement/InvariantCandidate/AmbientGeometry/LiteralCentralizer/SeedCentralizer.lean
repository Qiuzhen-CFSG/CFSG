module

public import CFSG.Quasithin.Chapter1.Section03.Terminal.LinearFourActions.JankoFourStabilizer.InvariantMathieuGeometry.Max1Placement.InvariantCandidate.AmbientGeometry.LiteralCentralizer.Reduction
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.MathieuSeedCentralizer
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.MathieuSeedCentralizer.AmbientOrder

/-!
# The ambient centralizer of the literal max1 seed

The local 276-point orbit calculation produces enough centralizing elements
inside literal max1. The intrinsic ten-dimensional action bounds the full
matrix centralizer by the same order, 1816657920. Order comparison therefore
places every ambient element centralizing the literal seed `(xy)^14` in max1.
The conditional order-comparison interface is retained below, followed by
its unconditional assembly from the proved ambient bound.

Source: the literal ATLAS max1 word in `LiteralCentralizer.Reduction` and
the expected 2B centralizer in GLS3 Table 5.3i, printed p.270.
-/

public section

namespace CFSG.Quasithin.Chapter1.Terminal.LinearFourActions.JankoFourStabilizer.Max1Placement.AmbientGeometry

/-- Conditional assembly from a full ambient centralizer order bound. -/
theorem literalSeedCentralizerBound_of_card_le
    (hcard : Nat.card (Janko4.LocalStructure.MathieuSeedCentralizer.ambientSeedCentralizer
      Janko4.matrixA_mul_self Janko4.matrixB_pow_four) ≤ 1816657920) :
    LiteralSeedCentralizerBound :=
  Janko4.LocalStructure.MathieuSeedCentralizer.ambientSeedCentralizer_le_max1_of_card_le
    Janko4.matrixA_mul_self Janko4.matrixB_pow_four hcard

/-- The full ambient centralizer of the literal seed `(xy)^14` lies in max1. -/
theorem literalSeedCentralizerBound : LiteralSeedCentralizerBound :=
  literalSeedCentralizerBound_of_card_le
    Janko4.LocalStructure.MathieuSeedCentralizer.ambientSeedCentralizer_card_le

end CFSG.Quasithin.Chapter1.Terminal.LinearFourActions.JankoFourStabilizer.Max1Placement.AmbientGeometry
