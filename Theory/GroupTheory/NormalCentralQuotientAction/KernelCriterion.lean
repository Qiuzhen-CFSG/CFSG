module

public import Theory.GroupTheory.NormalCentralQuotientAction

/-!
# When the two central quotients agree

If G/N is centerless, the preimage of its center is exactly N. Consequently
G/Z(G) → G/centralPreimage(N) is injective precisely when N is central.
Surjectivity or centerlessness of G/N alone does not suffice.

This is the kernel comparison in Aschbacher–Smith, Corollary A.2.6,
printed p.34 of `refs/quasithin.pdf`, with N = O₂(L).
-/

public section
open Subgroup

namespace Subgroup
variable {G : Type*} [Group G]

theorem centralPreimage_eq_of_center_quotient_eq_bot (N : Subgroup G) [N.Normal]
    (hc : center (G ⧸ N) = ⊥) : centralPreimage N = N := by
  change (center (G ⧸ N)).comap (QuotientGroup.mk' N) = N
  rw [hc]
  exact QuotientGroup.ker_mk' N

theorem centralQuotientProjection_injective_iff_of_center_quotient_eq_bot
    (N : Subgroup G) [N.Normal] (hc : center (G ⧸ N) = ⊥) :
    Function.Injective (centralQuotientProjection N) ↔ N ≤ center G := by
  rw [centralQuotientProjection_injective_iff,
    centralPreimage_eq_of_center_quotient_eq_bot N hc]
  have hz : center G ≤ N := by
    rw [← centralPreimage_eq_of_center_quotient_eq_bot N hc]
    exact center_le_centralPreimage N
  exact ⟨fun h => h.symm.le, fun h => le_antisymm hz h⟩

end Subgroup
