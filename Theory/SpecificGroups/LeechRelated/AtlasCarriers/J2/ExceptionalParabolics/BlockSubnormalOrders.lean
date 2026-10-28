module

public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.ExceptionalParabolics.BlockSubnormalOrders.Residual
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.ExceptionalParabolics.BlockSubnormalOrders.CubicAction
public import Theory.GroupTheory.PResidual.SubnormalNineQuotient

/-!
# Subnormal two-perfect subgroups of the second Hall--Janko normalizer

The actual two-residual has intrinsic core quotient of order nine. Subnormal
core intersection and two-perfection therefore restrict the intrinsic quotient
orders to one, three and nine, with the first case forcing triviality. In the
cubic case, relative subnormality makes the radical normalize the subgroup;
Cauchy's theorem and the checked cubic commutator bound force order above 12.

This is the native calculation consumed by the Hall--Janko local block cover
in Aschbacher--Smith 2.3.9(7), printed p.526. The ambient group is precisely
`Seed.p₂`, the full second normalizer in the unchanged ATLAS J₂ carrier, and
subnormality is relative to it. All cores remain intrinsic.
-/

public section
namespace Sporadic.LeechRelated.J2.ExceptionalParabolics.BlockSubnormalOrders
open Subgroup Theory.GroupTheory Seed PairNormalizer

/-- The exact native subnormal order trichotomy for the full second normalizer. -/
theorem subnormal_orders (E : Subgroup p₂) (hE : E.IsSubnormal) (hp : IsPPerfect 2 E) :
    Nat.card E = 1 ∨
      (Nat.card (E ⧸ pCore 2 E) = 3 ∧ 12 < Nat.card E) ∨
        Nat.card (E ⧸ pCore 2 E) = 9 :=
  subnormal_orders_of_residual_nine_of_cubic_commutators (q₂.subgroupOf p₂)
    q₂_isPGroup.comap_subtype residual_core_quotient_card cubic_commutator_card E hE hp

end Sporadic.LeechRelated.J2.ExceptionalParabolics.BlockSubnormalOrders
