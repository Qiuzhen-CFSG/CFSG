module

public import Theory.AlgebraicGroup.Basic
public import Theory.AlgebraicGroup.Variety.Complete

/-!
# Morphic actions on possibly non-affine varieties

This module gives the smallest action boundary connecting the repository's presented affine
algebraic groups to the scheme-backed `Variety.Geometric` API.  A `MorphicAction` is an ordinary
action of `Variety.Point G` on rational points together with a genuine variety morphism
`G x X -> X` inducing exactly that action through `affinePointEquiv` and `prodPointEquiv`.

Geometric consequences such as closed stabilizers, closed orbits, and reduced fixed loci are
deliberately not stored in the structure.  They are theorems about morphic actions and must be
proved from the scheme geometry rather than supplied as extra certificates by callers.
-/

@[expose] public noncomputable section

namespace Theory.AlgebraicGroup.Variety.Geometric

universe u

variable {k : Type u} [Field k] [IsAlgClosed k]

/-- A morphic action of a presented affine algebraic group on a possibly non-affine variety.

The `MulAction` laws describe the point action, while `actionMorphism_apply` states that it is
induced by the genuine scheme morphism `actionMorphism : G x X -> X` under the affine and product
rational-point equivalences.
-/
structure MorphicAction (G : Theory.AlgebraicGroup.Variety k)
    [AlgebraicGroup G] (X : Geometric k) extends
    MulAction (Theory.AlgebraicGroup.Variety.Point G) (Point X) where
  /-- The variety morphism inducing the action. -/
  actionMorphism : Morphism (prod (ofAffine G) X) X
  /-- Compatibility between the scheme morphism and the point-level action. -/
  actionMorphism_apply : ∀ (g : Theory.AlgebraicGroup.Variety.Point G) (x : Point X),
    actionMorphism (prodPoint ((affinePointEquiv G).symm g) x) = smul g x

end Theory.AlgebraicGroup.Variety.Geometric
