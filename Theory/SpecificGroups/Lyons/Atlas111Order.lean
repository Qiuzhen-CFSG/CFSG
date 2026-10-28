module

public import Theory.SpecificGroups.Lyons.Atlas111OrderSetup

/-!
# Assembly of the Lyons matrix-group order certificates

The proposed count is 5859000000 subgroup elements times 8835156 cosets of
the concrete subgroup defined in `Atlas111OrderSetup`. Lagrange's equality
proves the resulting order once both counts have been certified about those
matrices. This module currently proves that implication; it does not assert
an unconditional order theorem before the two certificates are supplied.

Source for the subgroup: ATLAS of Finite Group Representations,
https://brauer.maths.qmul.ac.uk/Atlas/v3/subgroup/LyG1-max1W1 .
-/

namespace Lyons.OrderCertificate

/-- Combine the two concrete counting certificates. -/
public theorem card_eq_of_local_card_index
    (hcard : Nat.card localSubgroup = 5859000000)
    (hindex : localSubgroup.index = 8835156) :
    Nat.card LyonsGroup = 51765179004000000 := by
  rw [card_eq_local_card_mul_index, hcard, hindex]

end Lyons.OrderCertificate
