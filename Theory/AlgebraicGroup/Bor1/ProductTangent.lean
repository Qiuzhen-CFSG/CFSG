module

public import Theory.AlgebraicGroup.Bor1.Differential
public import Theory.AlgebraicGroup.Product

/-!
# Identity tangents of direct products

This module gives the identity tangent space of a direct product its expected
factorwise decomposition.  Every derivation on `G x H` is the sum of the
tangents induced from the two canonical factor inclusions, and the differential
of a paired morphism is the corresponding sum of its component differentials.

The proof evaluates derivations on the two families of product coordinate
functions.  This provides the reusable formal product input for graph and
intersection arguments, including the characteristic-zero separability
constructions motivated by Bor1 Chapter 3, 9.1.
-/

universe u

namespace Theory.AlgebraicGroup.Bor1

open Theory.AlgebraicGroup

variable {k : Type u} [Field k] [IsAlgClosed k]

omit [IsAlgClosed k] in
/-- An identity-point derivation on a direct product is the sum of its two
factor tangents. -/
public theorem identityPointDerivation_prod_decomposition
    {G H : Variety k} [AlgebraicGroup G] [AlgebraicGroup H]
    (D : IdentityPointDerivation (Variety.prod G H)) :
    D =
      identityTangentMorphismLinearMap (AlgebraicGroup.Morphism.inl G H)
          (identityTangentMorphismLinearMap (AlgebraicGroup.Morphism.fst G H) D) +
        identityTangentMorphismLinearMap (AlgebraicGroup.Morphism.inr G H)
          (identityTangentMorphismLinearMap (AlgebraicGroup.Morphism.snd G H) D) := by
  apply coordinateTangentMap_injective (Variety.prod G H)
  funext i
  cases i with
  | inl i =>
      let a := Variety.PolynomialFunction.ofPolynomial (Variety.prod G H)
        (MvPolynomial.X (Sum.inl i))
      have hleft :
          (AlgebraicGroup.Morphism.fst G H).toVariety.pullbackAlgHom
              ((AlgebraicGroup.Morphism.inl G H).toVariety.pullbackAlgHom a) = a := by
        apply Variety.PolynomialFunction.ext
        intro x
        simp [a, Variety.Morphism.pullbackAlgHom,
          Variety.Morphism.pullbackRingHom, Variety.PolynomialFunction.pullback,
          AlgebraicGroup.Morphism.inl, AlgebraicGroup.Morphism.fst,
          Variety.PolynomialFunction.ofPolynomial,
          Variety.PolynomialFunction.toFun, Variety.prodPointEquiv,
          evalPolynomial]
      have hright :
          (AlgebraicGroup.Morphism.snd G H).toVariety.pullbackAlgHom
              ((AlgebraicGroup.Morphism.inr G H).toVariety.pullbackAlgHom a) =
            algebraMap k (Variety.PolynomialFunction (Variety.prod G H))
              ((1 : Variety.Point G).val i) := by
        apply Variety.PolynomialFunction.ext
        intro x
        simp [a, Variety.Morphism.pullbackAlgHom,
          Variety.Morphism.pullbackRingHom, Variety.PolynomialFunction.pullback,
          AlgebraicGroup.Morphism.inr, AlgebraicGroup.Morphism.snd,
          Variety.PolynomialFunction.ofPolynomial,
          Variety.PolynomialFunction.toFun, Variety.prodPointEquiv,
          evalPolynomial]
        exact (polynomialFunction_algebraMap_apply (Variety.prod G H)
          ((1 : Variety.Point G).val i) x).symm
      change D a = D ((AlgebraicGroup.Morphism.fst G H).toVariety.pullbackAlgHom
          ((AlgebraicGroup.Morphism.inl G H).toVariety.pullbackAlgHom a)) +
        D ((AlgebraicGroup.Morphism.snd G H).toVariety.pullbackAlgHom
          ((AlgebraicGroup.Morphism.inr G H).toVariety.pullbackAlgHom a))
      rw [hleft, hright, D.map_algebraMap, add_zero]
  | inr i =>
      let a := Variety.PolynomialFunction.ofPolynomial (Variety.prod G H)
        (MvPolynomial.X (Sum.inr i))
      have hleft :
          (AlgebraicGroup.Morphism.fst G H).toVariety.pullbackAlgHom
              ((AlgebraicGroup.Morphism.inl G H).toVariety.pullbackAlgHom a) =
            algebraMap k (Variety.PolynomialFunction (Variety.prod G H))
              ((1 : Variety.Point H).val i) := by
        apply Variety.PolynomialFunction.ext
        intro x
        simp [a, Variety.Morphism.pullbackAlgHom,
          Variety.Morphism.pullbackRingHom, Variety.PolynomialFunction.pullback,
          AlgebraicGroup.Morphism.inl, AlgebraicGroup.Morphism.fst,
          Variety.PolynomialFunction.ofPolynomial,
          Variety.PolynomialFunction.toFun, Variety.prodPointEquiv,
          evalPolynomial]
        exact (polynomialFunction_algebraMap_apply (Variety.prod G H)
          ((1 : Variety.Point H).val i) x).symm
      have hright :
          (AlgebraicGroup.Morphism.snd G H).toVariety.pullbackAlgHom
              ((AlgebraicGroup.Morphism.inr G H).toVariety.pullbackAlgHom a) = a := by
        apply Variety.PolynomialFunction.ext
        intro x
        simp [a, Variety.Morphism.pullbackAlgHom,
          Variety.Morphism.pullbackRingHom, Variety.PolynomialFunction.pullback,
          AlgebraicGroup.Morphism.inr, AlgebraicGroup.Morphism.snd,
          Variety.PolynomialFunction.ofPolynomial,
          Variety.PolynomialFunction.toFun, Variety.prodPointEquiv,
          evalPolynomial]
      change D a = D ((AlgebraicGroup.Morphism.fst G H).toVariety.pullbackAlgHom
          ((AlgebraicGroup.Morphism.inl G H).toVariety.pullbackAlgHom a)) +
        D ((AlgebraicGroup.Morphism.snd G H).toVariety.pullbackAlgHom
          ((AlgebraicGroup.Morphism.inr G H).toVariety.pullbackAlgHom a))
      rw [hleft, hright, D.map_algebraMap, zero_add]

/-- The differential of a paired algebraic-group morphism is the sum of its
two component differentials in the product tangent space. -/
public theorem identityTangentMorphismLinearMap_prod_apply
    {X G H : Variety k} [AlgebraicGroup X] [AlgebraicGroup G]
    [AlgebraicGroup H] (f : AlgebraicGroup.Morphism X G)
    (g : AlgebraicGroup.Morphism X H) (D : IdentityPointDerivation X) :
    identityTangentMorphismLinearMap (AlgebraicGroup.Morphism.prod f g) D =
      identityTangentMorphismLinearMap (AlgebraicGroup.Morphism.inl G H)
          (identityTangentMorphismLinearMap f D) +
        identityTangentMorphismLinearMap (AlgebraicGroup.Morphism.inr G H)
          (identityTangentMorphismLinearMap g D) := by
  let pair := AlgebraicGroup.Morphism.prod f g
  have hfst : (AlgebraicGroup.Morphism.fst G H).comp pair = f := by
    apply AlgebraicGroup.Morphism.ext
    funext x
    rfl
  have hsnd : (AlgebraicGroup.Morphism.snd G H).comp pair = g := by
    apply AlgebraicGroup.Morphism.ext
    funext x
    rfl
  calc
    identityTangentMorphismLinearMap pair D =
        identityTangentMorphismLinearMap (AlgebraicGroup.Morphism.inl G H)
            (identityTangentMorphismLinearMap (AlgebraicGroup.Morphism.fst G H)
              (identityTangentMorphismLinearMap pair D)) +
          identityTangentMorphismLinearMap (AlgebraicGroup.Morphism.inr G H)
            (identityTangentMorphismLinearMap (AlgebraicGroup.Morphism.snd G H)
              (identityTangentMorphismLinearMap pair D)) :=
      identityPointDerivation_prod_decomposition _
    _ = identityTangentMorphismLinearMap (AlgebraicGroup.Morphism.inl G H)
            (identityTangentMorphismLinearMap
              ((AlgebraicGroup.Morphism.fst G H).comp pair) D) +
          identityTangentMorphismLinearMap (AlgebraicGroup.Morphism.inr G H)
            (identityTangentMorphismLinearMap
              ((AlgebraicGroup.Morphism.snd G H).comp pair) D) := by
      rw [identityTangentMorphismLinearMap_comp,
        identityTangentMorphismLinearMap_comp]
      rfl
    _ = _ := by rw [hfst, hsnd]

end Theory.AlgebraicGroup.Bor1
