module

public import CFSG.Quasithin.Chapter16.Section03.EnlargementSieve.IntrinsicRanks.G2Cover
public import CFSG.Quasithin.ChapterI.Section02.ExceptionalCovers

/-!
# Discharging the double-G₂ enlargement's two-central lifting input

The actual central quotient and center order supplied in the double-G₂(4)
case suffice for the rank-five lower bound. The long-root-plane proof of
I.2.2(5a) discharges the former `CentralInvolutionLifting` premise. The
non-two-central order-four input to the separate normalizer-square theorem
is not used or asserted here.

Source: Aschbacher–Smith 16.3.9, printed pp.1180–1181, using I.2.2(5a).
-/

public section
namespace CFSG.Quasithin.Chapter16.EnlargementSieve.IntrinsicRanks.G2Cover
open Subgroup Theory.GroupTheory
variable {G F : Type*} [Group G] [Finite G] [Field F] [Finite F] [CharP F 2]

/-- The double-G₂(4) enlargement has rank at least five without a lifting premise. -/
theorem enlargement_rank_ge_five_of_center_card_two (t : G) (L : Subgroup G)
    (e : (enlargement t L ⧸ center (enlargement t L)) ≃* Atlas.G2.Model F)
    (hF : Nat.card F = 4) (hZ : Nat.card (center (enlargement t L)) = 2) :
    5 ≤ primeRank 2 (enlargement t L) :=
  enlargement_rank_ge_five t L e hF hZ
    (ChapterI.Section02.ExceptionalCovers.g2_twoCentral_involutions_lift_of_center_card_two
      e hF hZ)

end CFSG.Quasithin.Chapter16.EnlargementSieve.IntrinsicRanks.G2Cover
