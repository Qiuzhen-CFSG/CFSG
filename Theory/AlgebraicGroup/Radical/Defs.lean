module

public import Mathlib.GroupTheory.Solvable
public import Theory.AlgebraicGroup.ClosedSubgroup.Basic

universe u

/-! Radical subgroups of algebraic groups. -/

namespace Theory.AlgebraicGroup

variable {k : Type u} [Field k]

/-- Definition 1.7.1: a radical subgroup is a largest connected normal
solvable closed subgroup. -/
@[expose]
public def IsRadicalSubgroup {G : Variety k} [AlgebraicGroup G]
    (R : ClosedSubgroup G) : Prop :=
  R.toSubgroup.Normal ∧
    _root_.IsConnected (R : Set (Variety.Point G)) ∧
      Group.IsSolvable (Variety.Point R.carrierVariety) ∧
        ∀ N : ClosedSubgroup G,
          N.toSubgroup.Normal →
          _root_.IsConnected (N : Set (Variety.Point G)) →
          Group.IsSolvable (Variety.Point N.carrierVariety) →
          N ≤ R

/-- A radical subgroup is connected. -/
public lemma IsRadicalSubgroup.connected
    {G : Variety k} [AlgebraicGroup G] {R : ClosedSubgroup G}
    (hR : IsRadicalSubgroup R) :
    _root_.IsConnected (R : Set (Variety.Point G)) :=
  hR.2.1

/-- A radical subgroup is normal in the ambient algebraic group. -/
public lemma IsRadicalSubgroup.normal
    {G : Variety k} [AlgebraicGroup G] {R : ClosedSubgroup G}
    (hR : IsRadicalSubgroup R) :
    R.toSubgroup.Normal :=
  hR.1

/-- A radical subgroup has a solvable point group. -/
public lemma IsRadicalSubgroup.solvable
    {G : Variety k} [AlgebraicGroup G] {R : ClosedSubgroup G}
    (hR : IsRadicalSubgroup R) :
    Group.IsSolvable (Variety.Point R.carrierVariety) :=
  hR.2.2.1

/-- A radical subgroup contains every connected normal solvable closed
subgroup. -/
public lemma IsRadicalSubgroup.maximal
    {G : Variety k} [AlgebraicGroup G] {R : ClosedSubgroup G}
    (hR : IsRadicalSubgroup R) (N : ClosedSubgroup G)
    (hNnormal : N.toSubgroup.Normal)
    (hNconnected : _root_.IsConnected (N : Set (Variety.Point G)))
    (hNsolvable : Group.IsSolvable (Variety.Point N.carrierVariety)) :
    N ≤ R :=
  hR.2.2.2 N hNnormal hNconnected hNsolvable

/-- Radical subgroups of an algebraic group are equal. -/
public lemma IsRadicalSubgroup.eq
    {G : Variety k} [AlgebraicGroup G] {R S : ClosedSubgroup G}
    (hR : IsRadicalSubgroup R) (hS : IsRadicalSubgroup S) :
    R = S := by
  apply SetLike.coe_injective
  exact Set.Subset.antisymm
    (hS.maximal R hR.normal hR.connected hR.solvable)
    (hR.maximal S hS.normal hS.connected hS.solvable)

end Theory.AlgebraicGroup
