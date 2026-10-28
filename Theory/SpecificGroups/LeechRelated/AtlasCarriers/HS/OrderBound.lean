module

public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.HS.OrderBound.Certificate

/-!
# An order bound for the ATLAS Higman–Sims permutation carrier

The subgroup of the two defining permutations has order dividing
`2^9 * 3^2 * 5^3 * 7 * 11`, the order in GLS volume 3, Table 5.3m,
printed p.274. The permutations are exactly those of ATLAS HSG1-p100B0,
with the action conventions and attribution recorded in the carrier module.

We place the defining subgroup inside a concrete group with additional
permutation generators. A kernel-checked stabilizer-chain certificate counts
that group: its successive indices are 100, 22, 21, 20, 16 and 3, and its
terminal subgroup is trivial. Lagrange's theorem then gives the divisibility
bound. No membership of the additional generators in the defining subgroup,
simplicity assumption, or comparison with a lattice model is needed.

The discovery scripts and their untrusted permutation witnesses are retained
in `OrderBound/source/`. Every inverse law, representative image and transition
identity used in the count is checked in Lean on all 100 letters.
-/

namespace Sporadic.LeechRelated.HS

/-- The exact degree-100 ATLAS carrier satisfies the tabulated order bound. -/
public theorem card_carrier_dvd :
    Nat.card Carrier ∣ 2 ^ 9 * 3 ^ 2 * 5 ^ 3 * 7 * 11 := by
  have h := Subgroup.card_dvd_of_le OrderCertificate.generated_le
  rw [OrderCertificate.H0_card] at h
  exact h

end Sporadic.LeechRelated.HS
