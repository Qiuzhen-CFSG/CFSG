module

public import Theory.SpecificGroups.Held.AutomorphismLocalPair.SubnormalLarge.ResidualNine
public import Theory.SpecificGroups.Held.AutomorphismLocalPair.SubnormalLarge

/-!
# Applying the pair quotient reduction to subnormal Held subgroups

The proved literal comparison and quotient-map certificates supply exactly the
residual-nine premise of `representative_subnormal_orders_of_calculations`.
The separately owned cubic commutator bound remains explicit. No ambient
normality is substituted for the consumer's relative subnormality.

Source: Aschbacher--Smith 2.3.9(7), printed p.526; GLS3 Table 5.3p.
-/

public section
namespace Held.AutomorphismLocalPair
open Subgroup LocalPairs.PairCoverage.LocalActions.Exhaustion ResidualNine

/-- The two finite pair certificates feed the unchanged subnormal-order consumer. -/
theorem representative_subnormal_orders_of_pair_quotient
    (hcomparison : representativeLargeLocal.map (MulAut.conj pairConjugator).toMonoidHom =
      candidateProduct false 0)
    (f : candidateProduct false 0 →* QuotientModel)
    (hf : Function.Surjective f) (hk : IsPGroup 2 f.ker)
    (hcubic : ∀ x : representativeLargeLocal, orderOf x = 3 →
      12 < Nat.card (⁅representativeLargeKernel, zpowers x⁆ :
        Subgroup representativeLargeLocal))
    (E : Subgroup representativeLargeLocal) (hE : E.IsSubnormal)
    (hp : IsPPerfect 2 E) :
    Nat.card E = 1 ∨
      (Nat.card (E ⧸ pCore 2 E) = 3 ∧ 12 < Nat.card E) ∨
        Nat.card (E ⧸ pCore 2 E) = 9 :=
  representative_subnormal_orders_of_calculations
    (representative_residual_core_quotient_card_of_pair_quotient hcomparison f hf hk)
    hcubic E hE hp

/-- The unconditional residual calculation discharges the numerical premise
of the actual relative-subnormal consumer. Only its cubic bound remains. -/
theorem representative_subnormal_orders_of_cubic_commutators
    (hcubic : ∀ x : representativeLargeLocal, orderOf x = 3 →
      12 < Nat.card (⁅representativeLargeKernel, zpowers x⁆ :
        Subgroup representativeLargeLocal))
    (E : Subgroup representativeLargeLocal) (hE : E.IsSubnormal)
    (hp : IsPPerfect 2 E) :
    Nat.card E = 1 ∨
      (Nat.card (E ⧸ pCore 2 E) = 3 ∧ 12 < Nat.card E) ∨
        Nat.card (E ⧸ pCore 2 E) = 9 :=
  representative_subnormal_orders_of_calculations
    representative_residual_core_quotient_card hcubic E hE hp

end Held.AutomorphismLocalPair
