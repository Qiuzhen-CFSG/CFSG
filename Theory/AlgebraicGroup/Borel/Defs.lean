module

public import Mathlib.GroupTheory.Solvable
public import Theory.AlgebraicGroup.ClosedSubgroup.Basic

universe u

/-! Borel subgroups of algebraic groups. -/

namespace Theory.AlgebraicGroup

variable {k : Type u} [Field k]

/-- Definition 1.6.1: a Borel subgroup is maximal among connected solvable
closed subgroups. -/
@[expose]
public def IsBorelSubgroup {G : Variety k} [AlgebraicGroup G]
    (B : ClosedSubgroup G) : Prop :=
  _root_.IsConnected (B : Set (Variety.Point G)) ∧
    Group.IsSolvable (Variety.Point B.carrierVariety) ∧
      ∀ S : ClosedSubgroup G,
        _root_.IsConnected (S : Set (Variety.Point G)) →
        Group.IsSolvable (Variety.Point S.carrierVariety) →
        B ≤ S → S = B

/-- A Borel subgroup is connected. -/
public lemma IsBorelSubgroup.connected
    {G : Variety k} [AlgebraicGroup G] {B : ClosedSubgroup G}
    (hB : IsBorelSubgroup B) :
    _root_.IsConnected (B : Set (Variety.Point G)) :=
  hB.1

/-- A Borel subgroup has a solvable group of points. -/
public lemma IsBorelSubgroup.solvable
    {G : Variety k} [AlgebraicGroup G] {B : ClosedSubgroup G}
    (hB : IsBorelSubgroup B) :
    Group.IsSolvable (Variety.Point B.carrierVariety) :=
  hB.2.1

/-- A Borel subgroup is maximal among connected solvable closed subgroups. -/
public lemma IsBorelSubgroup.maximal
    {G : Variety k} [AlgebraicGroup G] {B : ClosedSubgroup G}
    (hB : IsBorelSubgroup B) :
    ∀ S : ClosedSubgroup G,
      _root_.IsConnected (S : Set (Variety.Point G)) →
      Group.IsSolvable (Variety.Point S.carrierVariety) →
      B ≤ S → S = B :=
  hB.2.2

end Theory.AlgebraicGroup
