module

public import Theory.AlgebraicGroup.Borel.Defs

universe u

/-! Parabolic subgroups of algebraic groups. -/

namespace Theory.AlgebraicGroup

variable {k : Type u} [Field k]

/-- A closed subgroup is parabolic when it contains a Borel subgroup. -/
@[expose]
public def IsParabolicSubgroup
    {G : Variety k} [AlgebraicGroup G] (P : ClosedSubgroup G) : Prop :=
  ∃ B : ClosedSubgroup G, IsBorelSubgroup B ∧ B ≤ P

/-- Every Borel subgroup is parabolic. -/
public lemma IsBorelSubgroup.isParabolic
    {G : Variety k} [AlgebraicGroup G] {B : ClosedSubgroup G}
    (hB : IsBorelSubgroup B) :
    IsParabolicSubgroup B :=
  ⟨B, hB, fun _ hx => hx⟩

end Theory.AlgebraicGroup
