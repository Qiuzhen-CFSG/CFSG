module

public import Theory.AlgebraicGroup.Dimension.Defs
public import Theory.AlgebraicGroup.Radical.Defs

universe u

/-! Semisimple and simple algebraic groups. -/

namespace Theory.AlgebraicGroup

variable {k : Type u} [Field k]

/-- A semisimple algebraic group is connected and has trivial radical. -/
@[expose]
public def IsSemisimpleAlgebraicGroup
    (G : Variety k) [AlgebraicGroup G] : Prop :=
  _root_.IsConnected (Set.univ : Set (Variety.Point G)) ∧
    ∀ R : ClosedSubgroup G, IsRadicalSubgroup R → R.toSubgroup = ⊥

/-!
The GLS convention used here defines simplicity by connectedness, a nontrivial
derived subgroup, and dimension zero for every proper closed normal subgroup.
-/
@[expose]
public def IsSimpleAlgebraicGroup
    (G : Variety k) [AlgebraicGroup G] : Prop :=
  _root_.IsConnected (Set.univ : Set (Variety.Point G)) ∧
    ⁅(⊤ : Subgroup (Variety.Point G)), (⊤ : Subgroup (Variety.Point G))⁆ ≠
      (⊥ : Subgroup (Variety.Point G)) ∧
    ∀ N : ClosedSubgroup G,
      N.toSubgroup.Normal → N.toSubgroup ≠ ⊤ →
      Variety.dimension N.carrierVariety = 0

end Theory.AlgebraicGroup
