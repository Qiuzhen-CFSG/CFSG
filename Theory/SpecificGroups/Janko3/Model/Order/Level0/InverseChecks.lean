module

public import Theory.SpecificGroups.Janko3.Model.Order.Level0Data

/-!
# Finite checks for the inverse J3 transitions

The A rows agree. The B-inverse index table inverts the B table, and the paired
factor words fix points 1 and 2. These checks are used with the two-point base
of H1 in `Level0/Inverse`. Source: `Order/data/witnesses.json`.
-/

namespace Sporadic.Janko3.OrderCertificate.Level0
open Theory.GroupTheory
set_option maxRecDepth 40000
set_option Elab.async false

public theorem act2_eq : ∀ r, L0Act 2 r = L0Act 0 r := by
  apply allFin
  decide +kernel

public theorem factor2_eq : ∀ r, L0Factor 2 r = L0Factor 0 r := by
  apply allFin
  decide +kernel

public theorem act13 : ∀ r, L0Act 1 (L0Act 3 r) = r := by
  apply allFin
  decide +kernel

public theorem factor13_fix : ∀ r, ∀ j : Fin 2,
    (evalWord L1Gen (L0Factor 1 (L0Act 3 r)) * evalWord L1Gen (L0Factor 3 r))
      (if j = 0 then 1 else 2) = (if j = 0 then 1 else 2) := by
  apply allFin₂
  decide +kernel

end Sporadic.Janko3.OrderCertificate.Level0
