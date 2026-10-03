module

public import Theory.GroupTheory.BrauerSuzuki
public import Theory.GroupTheory.QuaternionSylowInvolution

/-!
# Centrality of involutions modulo the odd core

In a finite group with generalized quaternion Sylow two-subgroups, every
involution is central modulo the odd core. Brauer–Suzuki gives an even center
in the quotient; uniqueness of the quaternion Sylow involution then identifies
each involution with the central one.

This assembles the quotient-centrality consequence of Peterfalvi, Appendix II,
from the elementary bridge and Suzuki, *Group Theory II*, VI §2.2, Example 3.
The historical public name from `BenderSuzuki/PFAppendixII/proposition_1.lean`
is retained and re-exported there.
-/

namespace BenderSuzuki.PFAppendixII

open BenderSuzuki.PFAppendixIII

universe u

/-- An involution is central modulo the `2'`-core when a Sylow `2`-subgroup is
generalized quaternion. This is the quotient-centrality consequence of
Peterfalvi's Appendix II argument. -/
public theorem appendixII_quotient_involution_central_public
    {G : Type u} [Group G] [Finite G]
    (P : Sylow 2 G) {n : ℕ} (hn : 3 ≤ n)
    (hP : Nonempty (P ≃* QuaternionGroup (2 ^ (n - 2))))
    (u : G) (huI : IsInvolution u) :
    QuotientGroup.mk' (pPrimeCore 2 G) u ∈
      Subgroup.center (G ⧸ pPrimeCore 2 G) := by
  exact quotient_involution_central_of_even_center P hP
    (even_card_center_quotient_pPrimeCore_of_quaternion_sylow P hn hP) u huI

end BenderSuzuki.PFAppendixII
