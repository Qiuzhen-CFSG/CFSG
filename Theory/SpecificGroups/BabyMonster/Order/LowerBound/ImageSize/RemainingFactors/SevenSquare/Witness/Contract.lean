module

public import Theory.SpecificGroups.BabyMonster.Order.LowerBound.ImageSize.RemainingFactors.SevenSquare.Witness.Words
public import Theory.SpecificGroups.BabyMonster.Order.LowerBound.ImageSize.RemainingFactors.SevenSquare.Witness.Vectors

/-!
# The remaining concrete grid evaluations

These four families are the 28 row-vector equations for the fixed words and
vectors. They are the exact arithmetic input to the two-cycle constructor;
no full matrix orders or global commutation proofs are required.
-/

@[expose] public section
namespace BabyMonster.OrderLowerBound.RemainingFactors.SevenSquare
open LargePrimes

/-- The 28 remaining evaluations for the fixed candidate words and vectors. -/
structure Concrete.Transitions (ha : atlasA ^ 2 = 1) (hb : atlasB ^ 3 = 1) : Prop where
  xu : ∀ i, Matrix.vecMul (vector (Concrete.u i))
    ((Concrete.candidatePair ha hb).1.val : AtlasMatrix) = vector (Concrete.u (i+1))
  xw : ∀ j, Matrix.vecMul (vector (Concrete.w j))
    ((Concrete.candidatePair ha hb).1.val : AtlasMatrix) = vector (Concrete.w j)
  yu : ∀ i, Matrix.vecMul (vector (Concrete.u i))
    ((Concrete.candidatePair ha hb).2.val : AtlasMatrix) = vector (Concrete.u i)
  yw : ∀ j, Matrix.vecMul (vector (Concrete.w j))
    ((Concrete.candidatePair ha hb).2.val : AtlasMatrix) = vector (Concrete.w (j+1))

end BabyMonster.OrderLowerBound.RemainingFactors.SevenSquare
