module

public import Theory.AlgebraicGroup.Morphism.Basic
public import Theory.AlgebraicGroup.Morphism.Operations

universe u

/-!
# The Lang morphism

This small module contains the regular map underlying Lang's theorem.  For an
algebraic-group endomorphism `sigma`, the Lang morphism sends
`g` to `g * sigma(g⁻¹)`.  Later modules add finite-fiber, commutative
surjectivity, and solvable/semisimple reduction arguments.
-/

namespace Theory.AlgebraicGroup

variable {k : Type u} [Field k]

/-- The regular Lang morphism attached to an algebraic-group endomorphism. -/
@[expose]
public def langMorphism
    {K : Variety k} [AlgebraicGroup K]
    (sigma : AlgebraicGroup.Morphism K K) : Variety.Morphism K K :=
  (AlgebraicGroup.mulMorphism K).comp
    ((Variety.Morphism.id K).pair
      (sigma.toVariety.comp (AlgebraicGroup.invMorphism K)))

public theorem langMorphism_apply
    {K : Variety k} [AlgebraicGroup K]
    (sigma : AlgebraicGroup.Morphism K K) (g : Variety.Point K) :
    (langMorphism sigma).toFun g = g * sigma.onPoints g⁻¹ := by
  rfl

end Theory.AlgebraicGroup
