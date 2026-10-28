module

public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.HS
public import Theory.PGroupCore
public import Theory.GroupAction.AutomorphismFixedSubgroup
public import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.GroupTheory.Sylow

/-!
# Intrinsic geometry required for the HS block argument

This separates the finite permutation calculation from its transport through
a central two-cover and a component orbit. The intended seed is the normalizer
of the characteristic elementary subgroup of order eight in a Sylow two-group;
GLS3, Table 5.3m and the discussion on p.306, identify its shape as 4³.L₃(2).
An actual quotient isomorphism and self-centralization are required below;
the shape label is not a hypothesis or a proof of these properties.

The invariant seed must be stable under every automorphism stabilizing the
given Sylow subgroup. This is what permits adjoining the supplied ambient
Sylow subgroup, even when it permutes component conjugates. Generation uses
the fixed subgroup of the actual inner involution action. Transport must justify centralizing lifts. It suffices to lift the
two-residual of the fixed subgroup and use the Sylow subgroup already in the
seed. This is not an automatic property of a quotient map.

These are explicit remaining contracts for Aschbacher–Smith 2.3.9(7), p.526.
No inhabitant of `Geometry` or central-cover transport is
asserted here. Concrete construction and conditional transport are independent
prerequisites; the HS assembly owner must supply both.
-/

@[expose] public section

namespace Sporadic.LeechRelated.HS.BlockNormalizer
open Subgroup

/-- The intrinsic normalizer data used by the central-cover transport. -/
structure LocalSeed (R : Sylow 2 Carrier) (α : MulAut Carrier) where
  localSubgroup : Subgroup Carrier
  sylow_le : (R : Subgroup Carrier) ≤ localSubgroup
  invariant : ∀ β : MulAut Carrier,
    (R : Subgroup Carrier).map β.toMonoidHom = R →
      localSubgroup.map β.toMonoidHom = localSubgroup
  selfCentralizing : centralizer (pCore 2 localSubgroup : Set localSubgroup) ≤
    pCore 2 localSubgroup
  quotientIso : (localSubgroup ⧸ pCore 2 localSubgroup) ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)
  generated : α.fixedSubgroup ⊔ localSubgroup = ⊤

/-- Concrete HS facts still to prove. Centerlessness is needed to identify
the full center of a quasisimple lift with its retained two-kernel. -/
structure Geometry : Prop where
  center_eq_bot : center Carrier = ⊥
  seed : ∀ (R : Sylow 2 Carrier) (α : MulAut Carrier),
    orderOf α = 2 → α ∈ (MulAut.conj (G := Carrier)).range →
    (∀ r ∈ (R : Subgroup Carrier), α r = r) →
      Nonempty (LocalSeed R α)

end Sporadic.LeechRelated.HS.BlockNormalizer
