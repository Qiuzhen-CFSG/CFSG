module

public import Theory.SpecificGroups.BabyMonster.Order.LowerBound.ImageSize.RemainingFactors.SevenSquare.Grid

/-!
# Assembly of the square-of-seven vector certificate

A concrete grid of 49 distinct vectors, with the two certified cyclic shifts,
forces `7^2` to divide the standard ATLAS matrix subgroup's cardinality.
The concrete grid is a separate witness obligation; this module does not
assume the proposed ATLAS local subgroup identification.
-/

@[expose] public section
namespace BabyMonster.OrderLowerBound.RemainingFactors

/-- Discharge the square-of-seven divisor from concrete grid data. -/
theorem seven_sq_dvd_of_grid (ha : atlasA ^ 2 = 1) (hb : atlasB ^ 3 = 1)
    (hgrid : Nonempty (SevenSquare.GridCertificate ha hb)) :
    7 ^ 2 ∣ Nat.card (standardImage ha hb) := by
  obtain ⟨c⟩ := hgrid
  exact c.card_dvd

end BabyMonster.OrderLowerBound.RemainingFactors
