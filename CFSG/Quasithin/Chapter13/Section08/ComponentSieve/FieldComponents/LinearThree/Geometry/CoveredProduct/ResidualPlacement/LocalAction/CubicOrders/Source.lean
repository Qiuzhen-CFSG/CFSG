module
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.LinearThree.Geometry.CoveredProduct.ResidualPlacement.LocalAction.CubicOrders
/-!
# The original covered cubic residual order without a factorization premise

The literal source residual maps to the actual point commutator residual.
The source containment theorem proves the only formerly supplied use of
L₁=L₁,₊L₀. The checked intrinsic model order therefore gives the required
cubic quotient directly from the earlier natural action and Sylow data.
Source: Aschbacher–Smith, Notation13.2.1 and13.3.14(d), pp.877 and892.
-/
public section
open Subgroup
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.LinearThree.Geometry.CoveredProduct.ResidualPlacement.LocalAction
variable {G : Type*} [Group G] [Finite G] {L T V P U : Subgroup G}
theorem NaturalSetup.plus_core_card_source (d : NaturalSetup L T V P U) :
    Nat.card (plus L T P ⧸ pCore 2 (plus L T P)) = 3 := by
  rw [CubicOrders.plus_core_card_eq_model_source d]
  exact Representation.Hexacode.CubicLocalModel.Orders.commutatorResidual_quotient_card
    d.point (CubicOrders.coverSylow d) d.point_dim
    (CubicOrders.coverSylow_le_stabilizer d)
end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.LinearThree.Geometry.CoveredProduct.ResidualPlacement.LocalAction
