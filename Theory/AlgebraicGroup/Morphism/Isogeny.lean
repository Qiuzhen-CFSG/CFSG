module

public import Theory.AlgebraicGroup.Morphism.Basic

universe u

/-! Isogenies of algebraic groups. -/

namespace Theory.AlgebraicGroup

variable {k : Type u} [Field k]

@[expose]
public def IsIsogeny
    {G H : Variety k} [AlgebraicGroup G] [AlgebraicGroup H]
    (φ : AlgebraicGroup.Morphism G H) : Prop :=
  Function.Surjective φ.onPoints ∧ Finite φ.kernel

end Theory.AlgebraicGroup
