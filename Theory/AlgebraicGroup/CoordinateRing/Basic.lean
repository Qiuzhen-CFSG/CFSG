module

public import Theory.AlgebraicGroup.CoordinateRing.Point
public import Theory.AlgebraicGroup.Morphism.Operations

universe u

/-! Coordinate comultiplication, counit, and antipode maps of an algebraic group. -/

namespace Theory.AlgebraicGroup

open scoped TensorProduct

variable {k : Type u} [Field k]

/-- Pullback along multiplication, expressed in the tensor square of the
polynomial-function algebra. -/
@[expose]
public noncomputable def coordinateComultiplication
    (G : Variety k) [AlgebraicGroup G] :
    Variety.PolynomialFunction G →ₐ[k]
      Variety.PolynomialFunction G ⊗[k] Variety.PolynomialFunction G :=
  (polynomialFunction_prod_algEquiv G G).symm.toAlgHom.comp
    (AlgebraicGroup.mulMorphism G).pullbackAlgHom

/-- Evaluation at the identity point. -/
@[expose]
public def coordinateCounit
    (G : Variety k) [AlgebraicGroup G] :
    Variety.PolynomialFunction G →ₐ[k] k :=
  polynomialFunctionPointAlgHom G 1

/-- Pullback along inversion. -/
@[expose]
public def coordinateAntipode
    (G : Variety k) [AlgebraicGroup G] :
    Variety.PolynomialFunction G →ₐ[k] Variety.PolynomialFunction G :=
  (AlgebraicGroup.invMorphism G).pullbackAlgHom

/-- Evaluating the multiplication pullback at `(x,y)` gives `f(xy)`. -/
public lemma coordinateComultiplication_apply
    (G : Variety k) [AlgebraicGroup G]
    (f : Variety.PolynomialFunction G) (x y : Variety.Point G) :
    polynomialFunctionTensor G G
        (AlgebraicGroup.coordinateComultiplication G f)
        ((Variety.prodPointEquiv G G).symm (x, y)) =
      f (x * y) := by
  let e := polynomialFunction_prod_algEquiv G G
  let z := (Variety.prodPointEquiv G G).symm (x, y)
  calc
    polynomialFunctionTensor G G
        (AlgebraicGroup.coordinateComultiplication G f) z =
        ((AlgebraicGroup.mulMorphism G).pullbackAlgHom f) z := by
      change
        (e (e.symm ((AlgebraicGroup.mulMorphism G).pullbackAlgHom f))) z =
          ((AlgebraicGroup.mulMorphism G).pullbackAlgHom f) z
      exact congrArg
        (fun a : Variety.PolynomialFunction (Variety.prod G G) ↦ a z)
        (e.apply_symm_apply
          ((AlgebraicGroup.mulMorphism G).pullbackAlgHom f))
    _ = f (x * y) := by
      change f ((AlgebraicGroup.mulMorphism G).toFun z) = f (x * y)
      simp [z, AlgebraicGroup.mulMorphism, Variety.prodPointEquiv]

@[simp] public lemma coordinateCounit_apply
    (G : Variety k) [AlgebraicGroup G]
    (f : Variety.PolynomialFunction G) :
    coordinateCounit G f = f 1 :=
  polynomialFunctionPointAlgHom_apply G 1 f

@[simp] public lemma coordinateAntipode_apply
    (G : Variety k) [AlgebraicGroup G]
    (f : Variety.PolynomialFunction G) (x : Variety.Point G) :
    coordinateAntipode G f x = f x⁻¹ := by
  change f ((AlgebraicGroup.invMorphism G).toFun x) = f x⁻¹
  rfl

end Theory.AlgebraicGroup
