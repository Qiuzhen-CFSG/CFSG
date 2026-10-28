module

public import Theory.Mathieu.M12.SmallParabolicPair
public import Theory.GroupAction.AutomorphismFixedSubgroup

/-!
# Invariant second-parabolic seeds for the M₁₂ block argument

The model seed is an actual subgroup isomorphic to the marked natural-four
normalizer. It contains the prescribed Sylow subgroup, is invariant under
its automorphism stabilizer, has characteristic two, and generates M₁₂
together with the fixed subgroup of the specified inner involution.

These are explicit geometric premises for Aschbacher–Smith 2.3.9(7),
printed p.526, using GLS3 Table 5.3b. They contain no block-obstruction
conclusion. `SecondSquareControl` independently proves the intrinsic block
calculation. The seed construction and its transport through central covers
and component orbits remain separate obligations of the Chapter 2 assembly.
-/

@[expose] public section

namespace Sporadic.Mathieu.M12SmallPair.BlockGeometry
open Subgroup

/-- An invariant local subgroup in the specified M₁₂ carrier and Sylow marking. -/
structure LocalSeed (R : Sylow 2 M12) (α : MulAut M12) where
  localSubgroup : Subgroup M12
  modelIso : localSubgroup ≃* secondParabolic
  sylow_le : (R : Subgroup M12) ≤ localSubgroup
  invariant : ∀ β : MulAut M12,
    (R : Subgroup M12).map β.toMonoidHom = R →
      localSubgroup.map β.toMonoidHom = localSubgroup
  selfCentralizing : centralizer (pCore 2 localSubgroup : Set localSubgroup) ≤
    pCore 2 localSubgroup
  generated : α.fixedSubgroup ⊔ localSubgroup = ⊤

/-- The model geometry required by central-cover transport, still to be constructed. -/
structure Geometry : Prop where
  center_eq_bot : center M12 = ⊥
  seed : ∀ (R : Sylow 2 M12) (α : MulAut M12),
    orderOf α = 2 → α ∈ (MulAut.conj (G := M12)).range →
    (∀ r ∈ (R : Subgroup M12), α r = r) → Nonempty (LocalSeed R α)

end Sporadic.Mathieu.M12SmallPair.BlockGeometry

end
