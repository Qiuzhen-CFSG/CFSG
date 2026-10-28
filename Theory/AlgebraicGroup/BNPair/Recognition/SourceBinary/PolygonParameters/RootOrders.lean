module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.RootCoordinates.OrderFormulas

/-!
# Polygon parameter cardinality formulas

This file isolates the part of the finite rank-two calculation already
available from the split root coordinates.  If `qᵢ` denotes the cardinality of
the two simple roots, the ordered positive-root chart gives
`|U| = (q₀ q₁)³` in the hexagon case and `|U| = (q₀ q₁)⁴` in the octagon case.
These identities are useful inputs to the Feit--Higman spectral argument, but
do not themselves assert the square restrictions.

Source: Fong--Seitz I (1J), with the split BN-pair root-product calculation
from Carter §2.5 as formalized in `RootCoordinates.OrderFormulas`.
-/

public noncomputable section
open Subgroup
namespace Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates

variable {X : Type*} [Group X] {P : Fin 2 → Subgroup X}

/-- The exact positive-root cardinality product for a finite hexagon. -/
theorem hexagon_unipotent_card
    (Q : MarkedQuotient P) (split : SplitData Q.tits)
    (hm : rotationOrder Q = 6) :
    Nat.card split.U =
      (Nat.card (simpleRoot Q split 0) * Nat.card (simpleRoot Q split 1)) ^ 3 := by
  exact unipotent_card_even Q split 3 hm

/-- The exact positive-root cardinality product for a finite octagon. -/
theorem octagon_unipotent_card
    (Q : MarkedQuotient P) (split : SplitData Q.tits)
    (hm : rotationOrder Q = 8) :
    Nat.card split.U =
      (Nat.card (simpleRoot Q split 0) * Nat.card (simpleRoot Q split 1)) ^ 4 := by
  exact unipotent_card_even Q split 4 hm

end Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
