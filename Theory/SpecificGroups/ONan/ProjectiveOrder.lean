module

public import Theory.SpecificGroups.ONan.ProjectiveOrder.Setup

/-!
# Reducing the concrete O'Nan order to subgroup certificates

The ATLAS subgroup words specify a subgroup of `ONan.Model` independently of
any order assertion. A certificate of its order 3,753,792 and a certificate of
its index 122,760 suffice by Lagrange's equality. Neither numerical hypothesis
is asserted here: they are separate obligations for the concrete matrices.

See `ProjectiveOrder/Setup.lean` for the words and their source.
-/

namespace ONan

/-- Assemble the projective order from the two concrete subgroup certificates. -/
public theorem card_model_of_localSubgroup
    (horder : Nat.card OrderCertificate.localSubgroup = 3753792)
    (hindex : OrderCertificate.localSubgroup.index = 122760) :
    Nat.card Model = 460815505920 := by
  rw [OrderCertificate.card_model_eq, horder, hindex]

end ONan
