module

public import Theory.AlgebraicGroup.Tori.Basic

universe u

namespace Theory.AlgebraicGroup

variable {k : Type u} [Field k] [IsAlgClosed k]

/-- A closed subgroup is diagonalizable when it is isomorphic to a closed
subgroup of a standard diagonal torus.  Connectedness is not required. -/
@[expose]
public def IsDiagonalizableClosedSubgroup
    {G : Variety k} [AlgebraicGroup G] (S : ClosedSubgroup G) : Prop :=
  ∃ n : ℕ, ∃ D : ClosedSubgroup (dVariety k n),
    Nonempty (let _ := D.carrierAlgebraicGroup
      AlgebraicGroup.Iso S.carrierVariety D.carrierVariety)

end Theory.AlgebraicGroup
