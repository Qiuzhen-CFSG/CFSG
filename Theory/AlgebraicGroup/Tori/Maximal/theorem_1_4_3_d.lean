module

public import Theory.AlgebraicGroup.Tori.Maximal.theorem_1_4_3_b

/-!
This module isolates `theorem_1_4_3_d` from `Theory.AlgebraicGroup.Tori.Maximal`.
It retains the declarations following that unresolved result up to the next
unresolved result, preserving the source order and public API of the GLS3
algebraic-group development.
-/

universe u

set_option linter.style.haveILetI false

namespace Theory.AlgebraicGroup

variable {k : Type u} [Field k] [IsAlgClosed k]

set_option warningAsError false in
public theorem theorem_1_4_3_d
    {G H : Variety k} [AlgebraicGroup G] [AlgebraicGroup H]
    (φ : AlgebraicGroup.Morphism G H)
    (hφ : Function.Surjective φ.onPoints)
    (T : ClosedSubgroup G) (hT : IsMaximalTorus T) :
    IsMaximalTorus ((φ.comp T.inclusion).imageClosedSubgroup) := by sorry

end Theory.AlgebraicGroup
