module

public import Theory.SpecificGroups.Held.LocalPairs.PairCoverage.SylowOvergroups.RepresentativeChecks.LocalMembership
public import Theory.SpecificGroups.Held.LocalPairs.PairCoverage.SylowOvergroups.RepresentativeChecks.Obstructions

/-!
# Verification of the Held representative tests

All 4,831 fixed representatives satisfy the required alternative. The thirty
local rows belong to one of the two literal aligned overgroups, by certified
word identities in the faithful Held representation. Every other row has a
certified prime orbit, which constructs an actual element of prime order
different from two and three in the subgroup generated with the marking.

The branch selector exhausts the indices and assembles these two proved
families. The separate double-coset exhaustiveness and marked two-group
calculations are not premises here.

Sources: the ATLAS Held carrier and `SylowOvergroups/source/README.md`.
-/

namespace Held.LocalPairs.PairCoverage.SylowOvergroups

/-- Every fixed representative has actual aligned local membership or an
actual forbidden prime-order element in its join with the marked subgroup. -/
public theorem representativeChecks : RepresentativeChecks :=
  RepresentativeVerification.representativeChecks_of_branches
    RepresentativeVerification.localChecks RepresentativeVerification.obstructionChecks

end Held.LocalPairs.PairCoverage.SylowOvergroups
