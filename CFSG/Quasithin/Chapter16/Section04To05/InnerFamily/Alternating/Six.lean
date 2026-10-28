module

public import CFSG.Quasithin.Chapter16.Section04To05.InnerFamily.Alternating.Six.Setup
public import CFSG.Quasithin.Chapter16.Section04To05.InnerFamily.Alternating.Six.Action

/-!
# The constructed marked subgroup and terminal action for the A₆ branches

The marked product model gives the actual elementary subgroup A of order
sixteen, its four independent generators α = {z} ∪ (rᴸ ∩ A), and the total
product t. The corrected set β = zᴳ ∩ A carries its actual normalizer action,
with kernel C_G(A). The terminal helper combines the pair/triple exclusions,
fusion of t and normalizer transitivity with an order-six point stabilizer
to contradict the order-thirty obstruction in S₅.

This is an intermediate interface for source 16.4.9(2), not yet its A₆
nonemptiness theorem. Compatible Sylow placement, the conjugate overgroups
in `MarkedOvergroups`, the stabilizer calculation, and both branch-specific
transfer/fusion arguments must still be constructed. Final assembly remains
here; none of those obligations is discharged by the conditional helper.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
proof of 16.4.9(2), printed p.1192 (PDF p.1209). The reason for replacing
the printed zᴳ ∩ T by zᴳ ∩ A is proved in `SixSetCorrection`.
-/

public section

namespace CFSG.Quasithin.Chapter16.Intersections.Six

open Subgroup

variable {G : Type*} [Group G] [Finite G] {L : Subgroup G} {z r : G}

/-- Assemble the common terminal argument after the source branches have
proved their geometric and fusion obligations. -/
theorem contradiction_of_marked_fusion (M : AlternatingProductModel L z r 6)
    (hr : IsConj z r) (hexclusions : ProductExclusions M)
    (ht : IsConj z (total M)) (htrans : NormalizerTransitive M)
    (hs : Nat.card (normalizerStabilizer M) = 6) : False :=
  contradiction_of_five_points M
    (beta_card_of_total_conjugate M hr hexclusions.1 hexclusions.2 ht) htrans hs

end CFSG.Quasithin.Chapter16.Intersections.Six
