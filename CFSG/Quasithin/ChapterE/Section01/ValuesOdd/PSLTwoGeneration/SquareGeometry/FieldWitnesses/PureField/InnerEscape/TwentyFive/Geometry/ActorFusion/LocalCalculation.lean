module

public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSLTwoGeneration.SquareGeometry.FieldWitnesses.PureField.InnerEscape.TwentyFive.Geometry.ActorFusion.Inputs
public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSLTwoGeneration.SquareGeometry.FieldWitnesses.PureField.InnerEscape.TwentyFive.Geometry.ActorFusion.LocalCalculation.Coordinates
public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSLTwoGeneration.SquareGeometry.FieldWitnesses.PureField.InnerEscape.TwentyFive.Geometry.ActorFusion.LocalCalculation.SymmetricSpreading

/-!
# Characteristic-five local calculations

The intrinsic small-subgroup order and actual linear-kernel marking are
proved in `Coordinates`, together with transport of concrete symmetric-group
conjugators. `SymmetricSpreading` proves the finite conjugator calculation
for every factor of order two. Since the field involution has order two,
its cyclic group has exactly the required cardinality; this gives all three
clauses of `ActorFusion.LocalCalculation`, independently of the
pair-intersection calculation used by the full actor-fusion assembly.

Source: Aschbacher--Smith E.1.14(6), printed p.214, citing Asc82a Lemma 4.10.
-/

public section
noncomputable section
open Subgroup GorensteinWalter Matrix

namespace CFSG.Quasithin.ChapterE.ValuesOdd.PSLTwoGeneration.SquareGeometry.FieldWitnesses.PureField.InnerEscape.TwentyFive.Geometry.Frame

variable {F : Type*} [Field F] [Finite F] {σ : F ≃+* F}
variable (c : Frame σ) (hF : Nat.card F = 5 ^ 2) (hσ : orderOf σ = 2)

variable [Finite (innerModel F σ)]

/-- The intrinsic characteristic-five local calculation, with the finite
    symmetric-product conjugator discharged by the order-two field factor. -/
theorem localCalculation : ActorFusion.LocalCalculation c hF hσ := by
  apply localCalculation_of_symmetricSpreading c hF hσ
  exact symmetricSpreading_of_card_two (zpowers σ) (by
    rw [Nat.card_zpowers, hσ])

end CFSG.Quasithin.ChapterE.ValuesOdd.PSLTwoGeneration.SquareGeometry.FieldWitnesses.PureField.InnerEscape.TwentyFive.Geometry.Frame
