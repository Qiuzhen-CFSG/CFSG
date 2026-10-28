module

public import Theory.AlgebraicGroup.Variety.MorphicAction
public import Theory.AlgebraicGroup.Variety.AffineGeometricMorphism
public import Theory.AlgebraicGroup.Morphism.Basic

/-!
# Pulling back a morphic action

An algebraic-group morphism `H → G` pulls a morphic `G`-action back to `H`.
The action morphism is the composite of `H × X → G × X` with the original
action. This supplies, in particular, the restriction to a closed subgroup
used in the fixed-point argument of Borel, *Linear Algebraic Groups*, §10.4
(`refs/KGroup/Bor1/Chapter3.tex`).
-/

namespace Theory.AlgebraicGroup.Variety.Geometric

universe u

variable {k : Type u} [Field k] [IsAlgClosed k]
variable {G H : Theory.AlgebraicGroup.Variety k} [AlgebraicGroup G] [AlgebraicGroup H]
variable {X : Geometric k}

/-- Pullback of a morphic action along an algebraic-group morphism. -/
@[expose]
public noncomputable def MorphicAction.pullbackGroup (A : MorphicAction G X)
    (φ : Theory.AlgebraicGroup.Morphism H G) : MorphicAction H X := by
  letI := A.toMulAction
  letI : MulAction (Variety.Point H) (Point X) := MulAction.compHom _ φ.onPoints
  let p : Morphism (prod (ofAffine H) X) (prod (ofAffine G) X) :=
    Morphism.pair
      (Morphism.comp (fst (ofAffine H) X) (ofAffine_morphism φ.toVariety))
      (snd (ofAffine H) X)
  refine MorphicAction.mk inferInstance (Morphism.comp p A.actionMorphism) ?_
  intro h x
  have hfst :
      Morphism.comp (fst (ofAffine H) X) (ofAffine_morphism φ.toVariety)
          (prodPoint ((affinePointEquiv H).symm h) x) =
        (affinePointEquiv G).symm (φ.onPoints h) := by
    apply (affinePointEquiv G).injective
    rw [Morphism.comp_apply_point, fst_prodPoint, affinePointEquiv_ofAffine_morphism]
    simp only [Equiv.apply_symm_apply]
    rfl
  change A.actionMorphism (p (prodPoint ((affinePointEquiv H).symm h) x)) = _
  rw [Morphism.pair_apply, hfst, snd_prodPoint]
  exact A.actionMorphism_apply (φ.onPoints h) x

/-- The pulled-back action acts through the given point homomorphism. -/
@[simp]
public theorem MorphicAction.pullbackGroup_smul (A : MorphicAction G X)
    (φ : Theory.AlgebraicGroup.Morphism H G) (h : Variety.Point H) (x : Point X) :
    (A.pullbackGroup φ).toMulAction.smul h x = A.toMulAction.smul (φ.onPoints h) x := rfl

end Theory.AlgebraicGroup.Variety.Geometric
