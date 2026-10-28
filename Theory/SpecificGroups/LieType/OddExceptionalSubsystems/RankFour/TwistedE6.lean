module

public import Theory.SpecificGroups.LieType.OddExceptionalSubsystems.RankFour.TwistedE6.Witness
public import Theory.Quasithin.CentralExtensionRankFour

/-!
# Odd central covers of the actual twisted E6 models are not quasithin

For every odd defining prime and every field degree, the actual model has an
involution centralizing an elementary subgroup of order at least p⁴. Through
an arbitrary odd central kernel, the rank-four central-extension argument
produces an odd rank at least three in a genuine two-local subgroup upstairs.
This gives the original central-quotient endpoint without simplicity,
perfectness, quotient-quasithinness or multiplier assumptions.

Source: Aschbacher–Smith A.2.17, Case II, printed p.39.
-/

public noncomputable section
open Subgroup
namespace TwistedE6.RankFour
variable (p : ℕ) [Fact p.Prime] (m : ℕ)

theorem not_isQuasithin_of_quotient_equiv {G : Type*} [Group G] [Finite G]
    (hp2 : p ≠ 2) (iso : (G ⧸ center G) ≃* Model p m)
    (ho : Odd (Nat.card (center G))) : ¬ IsQuasithin G :=
  CentralExtension.not_isQuasithin_of_center_quotient_model iso ho hp2
    (involution_order p m hp2) (chartCentralizer p m)
    (chartCentralizer_injective p m hp2) (parameters_card_ge p m)

theorem not_isQuasithin_of_central_surjection {G : Type*} [Group G] [Finite G]
    (hp2 : p ≠ 2) (q : G →* Model p m) (hq : Function.Surjective q)
    (hc : q.ker ≤ center G) (ho : Odd (Nat.card q.ker)) : ¬ IsQuasithin G :=
  CentralExtension.not_isQuasithin_of_elementary_centralizer q hq hc ho hp2
    (involution_order p m hp2) (chartCentralizer p m)
    (chartCentralizer_injective p m hp2) (parameters_card_ge p m)

end TwistedE6.RankFour
