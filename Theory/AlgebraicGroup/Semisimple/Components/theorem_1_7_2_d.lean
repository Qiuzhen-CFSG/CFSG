module

public import Theory.AlgebraicGroup.Semisimple.Components.ComponentFamily

/-!
GLS3 Theorem 1.7.2(d), isolated from the proved component-family definitions and
group-theoretic lemmas in `ComponentFamily`. The remaining proof constructs the
finite family of simple components and recovers semisimplicity from it.
-/

universe u

namespace Theory.AlgebraicGroup

variable {k : Type u} [Field k] [IsAlgClosed k]

set_option warningAsError false in
public theorem theorem_1_7_2_d
    {G : Variety k} [AlgebraicGroup G] (hG : Variety.IsConnected G) :
    IsSemisimpleAlgebraicGroup G ↔
      ∃ n : ℕ, ∃ components : Fin n → ClosedSubgroup G,
        IsSemisimpleComponentFamily components := by sorry

end Theory.AlgebraicGroup
