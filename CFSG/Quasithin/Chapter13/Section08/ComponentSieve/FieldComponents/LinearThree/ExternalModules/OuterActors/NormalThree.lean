module

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.LinearThree.ExternalModules.OuterActors.Context
public import Theory.Representation.BinaryOffender.NormalThree

/-!
# Quadratic actors not centralizing the normal subgroup of order three

In the paired-module setup, a quadratic elementary two-subgroup which does not
centralize X has rank one and fixed codimension exactly half the module dimension.
The general calculation uses only the faithful action, normality and order of X,
and [U,X] = U. It is proved in `Theory.Representation.BinaryOffender.NormalThree`
by the order-three norm identity and rank-nullity for an inverting involution.

This discharges the normal-three input to
`OuterActors.paired_outer_bound_of_local_calculations`. It is one calculation in
the proof of Aschbacher–Smith 13.8.21(1), printed p.956, combined manuscript of
1 March 2004; the other outer-actor inputs and final source assembly are separate.
-/

public section

open Representation Representation.BinaryOffender

namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.LinearThree.ExternalModules.OuterActors

variable {H U : Type*} [Group H] [Finite H] [AddCommGroup U]
  [Module (ZMod 2) U] [FiniteDimensional (ZMod 2) U]

/-- The normal-three calculation for the actual paired-module action. -/
theorem paired_normalThree_quadratic_rank_fixedCodim
    (σ : Representation (ZMod 2) H U) (K X : Subgroup H)
    (eK : K ≃* BinaryLinearThree.Group) (h : PairedSetup σ K X eK)
    (A : Subgroup H) (hA : IsElementaryTwo A) (hq : IsQuadratic σ A)
    (hnot : ¬ A ≤ Subgroup.centralizer (X : Set H)) :
    rank A = 1 ∧ 2 * fixedCodim σ A = Module.finrank (ZMod 2) U :=
  normalThree_quadratic_rank_fixedCodim σ h.faithful X h.cyclic_normal
    h.cyclic_order h.moved A hA hq hnot

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.LinearThree.ExternalModules.OuterActors
