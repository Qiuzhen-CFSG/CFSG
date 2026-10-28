module

public import Theory.AlgebraicGroup.CoordinateRing.Hopf.Basic

/-!
# The coordinate Hopf algebra of an algebraic group

The coordinate algebra of an affine algebraic group is a Hopf algebra. Group
multiplication gives its comultiplication and evaluation at the identity gives
its counit.  Coassociativity is the coordinate form of associativity of group
multiplication.  The two counit laws are proved by evaluating elementary
tensors at `(1, x)` and `(x, 1)`.

The antipode is induced by inversion. The Hopf identities are checked by the
same rational-point extensionality API, evaluating the two convolution products
at `(x⁻¹, x)` and `(x, x⁻¹)`.

This whole-coordinate instance complements the stable-subalgebra bialgebra
construction in `CoordinateRing.Hopf.Basic` and lets lower algebraic layers use
standard coalgebra and convolution APIs directly.
-/

open scoped TensorProduct

universe u

namespace Theory.AlgebraicGroup

variable {k : Type u} [Field k]

/-- The canonical bialgebra structure on the coordinate algebra of an
algebraic group. -/
@[expose, instance_reducible]
public noncomputable def coordinateBialgebra
    (K : Variety k) [AlgebraicGroup K] :
    Bialgebra k (Variety.PolynomialFunction K) :=
  Bialgebra.ofAlgHom
    (coordinateComultiplication K)
    (coordinateCounit K)
    (coordinateComultiplication_coassoc K)
    (by
      apply AlgHom.ext
      intro f
      apply (Algebra.TensorProduct.lid k (Variety.PolynomialFunction K)).injective
      apply Variety.PolynomialFunction.ext
      intro x
      rw [AlgHom.comp_apply]
      let t := coordinateComultiplication K f
      have ht :
          (Algebra.TensorProduct.lid k (Variety.PolynomialFunction K)
            (Algebra.TensorProduct.map (coordinateCounit K)
              (.id k (Variety.PolynomialFunction K)) t)) x =
            polynomialFunctionTensor K K t
              ((Variety.prodPointEquiv K K).symm (1, x)) := by
        induction t using TensorProduct.induction_on with
        | zero => simp
        | add a b ha hb =>
            simpa [Variety.PolynomialFunction.toFun] using congrArg₂ (· + ·) ha hb
        | tmul a b =>
            rw [Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.lid_tmul,
              polynomialFunctionTensor_tmul, coordinateCounit_apply]
            simp [polynomialFunction_mul_apply, polynomialFunctionLeft_apply,
              polynomialFunctionRight_apply, polynomialFunction_smul_apply]
      calc
        _ = polynomialFunctionTensor K K t
              ((Variety.prodPointEquiv K K).symm (1, x)) := ht
        _ = f (1 * x) := coordinateComultiplication_apply K f 1 x
        _ = f x := by rw [one_mul]
        _ = (Algebra.TensorProduct.lid k (Variety.PolynomialFunction K)
              ((Algebra.TensorProduct.lid k (Variety.PolynomialFunction K)).symm f)) x := by
          exact congrArg (fun g : Variety.PolynomialFunction K => g x)
            ((Algebra.TensorProduct.lid k
              (Variety.PolynomialFunction K)).apply_symm_apply f).symm)
    (by
      apply AlgHom.ext
      intro f
      apply (Algebra.TensorProduct.rid k k (Variety.PolynomialFunction K)).injective
      apply Variety.PolynomialFunction.ext
      intro x
      rw [AlgHom.comp_apply]
      let t := coordinateComultiplication K f
      have ht :
          (Algebra.TensorProduct.rid k k (Variety.PolynomialFunction K)
            (Algebra.TensorProduct.map (.id k (Variety.PolynomialFunction K))
              (coordinateCounit K) t)) x =
            polynomialFunctionTensor K K t
              ((Variety.prodPointEquiv K K).symm (x, 1)) := by
        induction t using TensorProduct.induction_on with
        | zero => simp
        | add a b ha hb =>
            simpa [Variety.PolynomialFunction.toFun] using congrArg₂ (· + ·) ha hb
        | tmul a b =>
            rw [Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.rid_tmul,
              polynomialFunctionTensor_tmul, coordinateCounit_apply]
            simp only [polynomialFunction_mul_apply, polynomialFunctionLeft_apply,
              polynomialFunctionRight_apply, Equiv.apply_symm_apply, AlgHom.id_apply]
            rw [polynomialFunction_smul_apply]
            exact mul_comm _ _
      calc
        _ = polynomialFunctionTensor K K t
              ((Variety.prodPointEquiv K K).symm (x, 1)) := ht
        _ = f (x * 1) := coordinateComultiplication_apply K f x 1
        _ = f x := by rw [mul_one]
        _ = (Algebra.TensorProduct.rid k k (Variety.PolynomialFunction K)
              ((Algebra.TensorProduct.rid k k
                (Variety.PolynomialFunction K)).symm f)) x := by
          exact congrArg (fun g : Variety.PolynomialFunction K => g x)
            ((Algebra.TensorProduct.rid k k
              (Variety.PolynomialFunction K)).apply_symm_apply f).symm)

/-- The canonical Hopf algebra structure on the coordinate algebra of an
algebraic group. -/
@[expose, instance_reducible]
public noncomputable def coordinateHopfAlgebra
    (G : Variety k) [AlgebraicGroup G] :
    HopfAlgebra k G.PolynomialFunction := by
  letI : Bialgebra k G.PolynomialFunction := coordinateBialgebra G
  apply HopfAlgebra.ofAlgHom (coordinateAntipode G)
  · apply AlgHom.ext
    intro f
    apply Variety.PolynomialFunction.ext
    intro x
    rw [AlgHom.comp_apply, AlgHom.comp_apply]
    let t := coordinateComultiplication G f
    have ht :
        (Algebra.TensorProduct.lift
          (coordinateAntipode G)
          (.id k G.PolynomialFunction)
          (fun _ _ => Commute.all _ _) t) x =
          polynomialFunctionTensor G G t
            ((Variety.prodPointEquiv G G).symm (x⁻¹, x)) := by
      induction t using TensorProduct.induction_on with
      | zero => simp
      | add a b ha hb =>
          rw [map_add, map_add]
          simpa [Variety.PolynomialFunction.toFun] using
            congrArg₂ (· + ·) ha hb
      | tmul a b =>
          rw [Algebra.TensorProduct.lift_tmul]
          rw [polynomialFunctionTensor_tmul]
          simp [polynomialFunction_mul_apply, polynomialFunctionLeft_apply,
            polynomialFunctionRight_apply, coordinateAntipode_apply]
    calc
      (Algebra.TensorProduct.lift
          (coordinateAntipode G)
          (.id k G.PolynomialFunction)
          (fun _ _ => Commute.all _ _) t) x =
          polynomialFunctionTensor G G t
            ((Variety.prodPointEquiv G G).symm (x⁻¹, x)) := ht
      _ = f (x⁻¹ * x) := coordinateComultiplication_apply G f x⁻¹ x
      _ = f 1 := by rw [inv_mul_cancel]
      _ = (algebraMap k G.PolynomialFunction (coordinateCounit G f)) x := by
        rw [coordinateCounit_apply]
        exact polynomialFunction_algebraMap_apply G (f 1) x |>.symm
  · apply AlgHom.ext
    intro f
    apply Variety.PolynomialFunction.ext
    intro x
    rw [AlgHom.comp_apply, AlgHom.comp_apply]
    let t := coordinateComultiplication G f
    have ht :
        (Algebra.TensorProduct.lift
          (.id k G.PolynomialFunction)
          (coordinateAntipode G)
          (fun _ _ => Commute.all _ _) t) x =
          polynomialFunctionTensor G G t
            ((Variety.prodPointEquiv G G).symm (x, x⁻¹)) := by
      induction t using TensorProduct.induction_on with
      | zero => simp
      | add a b ha hb =>
          rw [map_add, map_add]
          simpa [Variety.PolynomialFunction.toFun] using
            congrArg₂ (· + ·) ha hb
      | tmul a b =>
          rw [Algebra.TensorProduct.lift_tmul]
          rw [polynomialFunctionTensor_tmul]
          simp [polynomialFunction_mul_apply, polynomialFunctionLeft_apply,
            polynomialFunctionRight_apply, coordinateAntipode_apply]
    calc
      (Algebra.TensorProduct.lift
          (.id k G.PolynomialFunction)
          (coordinateAntipode G)
          (fun _ _ => Commute.all _ _) t) x =
          polynomialFunctionTensor G G t
            ((Variety.prodPointEquiv G G).symm (x, x⁻¹)) := ht
      _ = f (x * x⁻¹) := coordinateComultiplication_apply G f x x⁻¹
      _ = f 1 := by rw [mul_inv_cancel]
      _ = (algebraMap k G.PolynomialFunction (coordinateCounit G f)) x := by
        rw [coordinateCounit_apply]
        exact polynomialFunction_algebraMap_apply G (f 1) x |>.symm

end Theory.AlgebraicGroup
