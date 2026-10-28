module

public import Mathlib.RingTheory.HopfAlgebra.Basic
public import Theory.AlgebraicGroup.CoordinateRing.Basic

universe u v

/-! Coordinate Hopf structures and their restriction to stable subalgebras. -/

namespace Theory.AlgebraicGroup

section
open scoped TensorProduct
variable {k : Type u} [Field k]

/-! Coordinate-algebra identifications for right-associated triple products. -/

@[expose]
public noncomputable def polynomialFunctionRightTripleAlgEquiv
    (G : Variety k) :
    Variety.PolynomialFunction G ⊗[k]
        (Variety.PolynomialFunction G ⊗[k] Variety.PolynomialFunction G) ≃ₐ[k]
      Variety.PolynomialFunction (Variety.prod G (Variety.prod G G)) :=
  (Algebra.TensorProduct.congr (AlgEquiv.refl)
      (polynomialFunction_prod_algEquiv G G)).trans
    (polynomialFunction_prod_algEquiv G (Variety.prod G G))

@[expose]
public noncomputable def polynomialFunctionLeftTripleAlgEquiv
    (G : Variety k) :
    (Variety.PolynomialFunction G ⊗[k] Variety.PolynomialFunction G) ⊗[k]
        Variety.PolynomialFunction G ≃ₐ[k]
      Variety.PolynomialFunction (Variety.prod (Variety.prod G G) G) :=
  (Algebra.TensorProduct.congr (polynomialFunction_prod_algEquiv G G)
      (AlgEquiv.refl)).trans
    (polynomialFunction_prod_algEquiv (Variety.prod G G) G)

@[simp]
public lemma polynomialFunctionRightTripleAlgEquiv_tmul_tensor_apply
    (G : Variety k) (f : Variety.PolynomialFunction G)
    (t : Variety.PolynomialFunction G ⊗[k] Variety.PolynomialFunction G)
    (x y z : Variety.Point G) :
    polynomialFunctionRightTripleAlgEquiv G (f ⊗ₜ[k] t)
      ((Variety.prodPointEquiv G (Variety.prod G G)).symm
        (x, (Variety.prodPointEquiv G G).symm (y, z))) =
      f x * polynomialFunctionTensor G G t
        ((Variety.prodPointEquiv G G).symm (y, z)) := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | add a b ha hb =>
      rw [TensorProduct.tmul_add, map_add, map_add]
      change _ + _ = f x * (_ + _)
      calc
        _ = f x * polynomialFunctionTensor G G a
              ((Variety.prodPointEquiv G G).symm (y, z)) +
            f x * polynomialFunctionTensor G G b
              ((Variety.prodPointEquiv G G).symm (y, z)) :=
          congrArg₂ (· + ·) ha hb
        _ = _ := (mul_add _ _ _).symm
  | tmul g h =>
      unfold polynomialFunctionRightTripleAlgEquiv
      rw [AlgEquiv.trans_apply]
      rw [Algebra.TensorProduct.congr_apply]
      rw [Algebra.TensorProduct.map_tmul]
      change polynomialFunction_prod_algEquiv G (Variety.prod G G)
          (f ⊗ₜ[k] polynomialFunction_prod_algEquiv G G (g ⊗ₜ[k] h))
            ((Variety.prodPointEquiv G (Variety.prod G G)).symm
              (x, (Variety.prodPointEquiv G G).symm (y, z))) = _
      rw [show polynomialFunction_prod_algEquiv G G (g ⊗ₜ[k] h) =
          polynomialFunctionTensor G G (g ⊗ₜ[k] h) by rfl]
      rw [show polynomialFunction_prod_algEquiv G (Variety.prod G G)
          (f ⊗ₜ[k] polynomialFunctionTensor G G (g ⊗ₜ[k] h)) =
          polynomialFunctionTensor G (Variety.prod G G)
            (f ⊗ₜ[k] polynomialFunctionTensor G G (g ⊗ₜ[k] h)) by rfl]
      rw [polynomialFunctionTensor_tmul, polynomialFunction_mul_apply,
        polynomialFunctionLeft_apply, polynomialFunctionRight_apply]
      rfl

@[simp]
public lemma polynomialFunctionRightTripleAlgEquiv_tmul_apply
    (G : Variety k) (f g h : Variety.PolynomialFunction G)
    (x y z : Variety.Point G) :
    polynomialFunctionRightTripleAlgEquiv G (f ⊗ₜ[k] (g ⊗ₜ[k] h))
      ((Variety.prodPointEquiv G (Variety.prod G G)).symm
        (x, (Variety.prodPointEquiv G G).symm (y, z))) =
      f x * (g y * h z) := by
  rw [polynomialFunctionRightTripleAlgEquiv_tmul_tensor_apply]
  simp only [polynomialFunctionTensor_tmul, polynomialFunction_mul_apply,
    polynomialFunctionLeft_apply, polynomialFunctionRight_apply,
    Variety.prodPointEquiv, Equiv.apply_symm_apply]

public lemma polynomialFunctionRightTripleAlgEquiv_assoc_tensor_tmul_apply
    (G : Variety k)
    (t : Variety.PolynomialFunction G ⊗[k] Variety.PolynomialFunction G)
    (h : Variety.PolynomialFunction G) (x y z : Variety.Point G) :
    polynomialFunctionRightTripleAlgEquiv G
      ((Algebra.TensorProduct.assoc k k k _ _ _) (t ⊗ₜ[k] h))
      ((Variety.prodPointEquiv G (Variety.prod G G)).symm
        (x, (Variety.prodPointEquiv G G).symm (y, z))) =
      polynomialFunctionTensor G G t
          ((Variety.prodPointEquiv G G).symm (x, y)) * h z := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | add a b ha hb =>
      rw [TensorProduct.add_tmul, map_add, map_add, map_add]
      change _ + _ = (_ + _) * h z
      calc
        _ = polynomialFunctionTensor G G a
              ((Variety.prodPointEquiv G G).symm (x, y)) * h z +
            polynomialFunctionTensor G G b
              ((Variety.prodPointEquiv G G).symm (x, y)) * h z :=
          congrArg₂ (· + ·) ha hb
        _ = _ := (add_mul _ _ _).symm
  | tmul f g => simp [mul_assoc]

public lemma polynomialFunctionRightTripleAlgEquiv_assoc_map_left_apply
    {G : Variety k} [AlgebraicGroup G]
    (t : Variety.PolynomialFunction G ⊗[k] Variety.PolynomialFunction G)
    (x y z : Variety.Point G) :
    polynomialFunctionRightTripleAlgEquiv G
      ((Algebra.TensorProduct.assoc k k k _ _ _)
        (Algebra.TensorProduct.map
          (coordinateComultiplication G)
          (.id k (Variety.PolynomialFunction G)) t))
      ((Variety.prodPointEquiv G (Variety.prod G G)).symm
        (x, (Variety.prodPointEquiv G G).symm (y, z))) =
      polynomialFunctionTensor G G t
        ((Variety.prodPointEquiv G G).symm (x * y, z)) := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | add a b ha hb =>
      rw [map_add, map_add, map_add, map_add]
      simpa [Variety.PolynomialFunction.toFun] using congrArg₂ (· + ·) ha hb
  | tmul f g =>
      rw [Algebra.TensorProduct.map_tmul]
      change polynomialFunctionRightTripleAlgEquiv G
          ((Algebra.TensorProduct.assoc k k k _ _ _)
            (coordinateComultiplication G f ⊗ₜ[k] g)) _ = _
      rw [polynomialFunctionRightTripleAlgEquiv_assoc_tensor_tmul_apply,
        coordinateComultiplication_apply, polynomialFunctionTensor_tmul]
      rfl

public lemma polynomialFunctionRightTripleAlgEquiv_map_right_apply
    {G : Variety k} [AlgebraicGroup G]
    (t : Variety.PolynomialFunction G ⊗[k] Variety.PolynomialFunction G)
    (x y z : Variety.Point G) :
    polynomialFunctionRightTripleAlgEquiv G
      (Algebra.TensorProduct.map
        (.id k (Variety.PolynomialFunction G))
        (coordinateComultiplication G) t)
      ((Variety.prodPointEquiv G (Variety.prod G G)).symm
        (x, (Variety.prodPointEquiv G G).symm (y, z))) =
      polynomialFunctionTensor G G t
        ((Variety.prodPointEquiv G G).symm (x, y * z)) := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | add a b ha hb =>
      rw [map_add, map_add, map_add]
      simpa [Variety.PolynomialFunction.toFun] using congrArg₂ (· + ·) ha hb
  | tmul f g =>
      rw [Algebra.TensorProduct.map_tmul]
      change polynomialFunctionRightTripleAlgEquiv G
          (f ⊗ₜ[k] coordinateComultiplication G g) _ = _
      rw [polynomialFunctionRightTripleAlgEquiv_tmul_tensor_apply,
        coordinateComultiplication_apply, polynomialFunctionTensor_tmul]
      rfl

@[simp]
public lemma polynomialFunctionLeftTripleAlgEquiv_tmul_apply
    (G : Variety k) (f g h : Variety.PolynomialFunction G)
    (x y z : Variety.Point G) :
    polynomialFunctionLeftTripleAlgEquiv G ((f ⊗ₜ[k] g) ⊗ₜ[k] h)
      ((Variety.prodPointEquiv (Variety.prod G G) G).symm
        ((Variety.prodPointEquiv G G).symm (x, y), z)) =
      (f x * g y) * h z := by
  unfold polynomialFunctionLeftTripleAlgEquiv
  rw [AlgEquiv.trans_apply]
  rw [Algebra.TensorProduct.congr_apply]
  rw [Algebra.TensorProduct.map_tmul]
  change polynomialFunction_prod_algEquiv (Variety.prod G G) G
      (polynomialFunction_prod_algEquiv G G (f ⊗ₜ[k] g) ⊗ₜ[k] h)
        ((Variety.prodPointEquiv (Variety.prod G G) G).symm
          ((Variety.prodPointEquiv G G).symm (x, y), z)) = _
  rw [show polynomialFunction_prod_algEquiv G G (f ⊗ₜ[k] g) =
      polynomialFunctionTensor G G (f ⊗ₜ[k] g) by rfl]
  rw [show polynomialFunction_prod_algEquiv (Variety.prod G G) G
      (polynomialFunctionTensor G G (f ⊗ₜ[k] g) ⊗ₜ[k] h) =
      polynomialFunctionTensor (Variety.prod G G) G
        (polynomialFunctionTensor G G (f ⊗ₜ[k] g) ⊗ₜ[k] h) by rfl]
  rw [polynomialFunctionTensor_tmul, polynomialFunction_mul_apply,
    polynomialFunctionLeft_apply, polynomialFunctionRight_apply]
  rw [polynomialFunctionTensor_tmul, polynomialFunction_mul_apply,
    polynomialFunctionLeft_apply, polynomialFunctionRight_apply]
  simp only [Variety.prodPointEquiv, Equiv.apply_symm_apply]

/-! Coassociativity of the coordinate comultiplication. -/

public lemma coordinateComultiplication_coassoc
    (G : Variety k) [AlgebraicGroup G] :
    (Algebra.TensorProduct.assoc k k k
        (Variety.PolynomialFunction G) (Variety.PolynomialFunction G)
        (Variety.PolynomialFunction G)).toAlgHom.comp
      ((Algebra.TensorProduct.map
        (coordinateComultiplication G)
        (.id k (Variety.PolynomialFunction G))).comp
        (coordinateComultiplication G)) =
    (Algebra.TensorProduct.map
      (.id k (Variety.PolynomialFunction G))
      (coordinateComultiplication G)).comp
        (coordinateComultiplication G) := by
  apply AlgHom.ext
  intro f
  apply (polynomialFunctionRightTripleAlgEquiv G).injective
  apply Variety.PolynomialFunction.ext
  intro q
  let outer := Variety.prodPointEquiv G (Variety.prod G G)
  let inner := Variety.prodPointEquiv G G
  generalize houter : outer q = xy
  obtain ⟨x, yz⟩ := xy
  generalize hinner : inner yz = yz'
  obtain ⟨y, z⟩ := yz'
  have hq : q = outer.symm (x, inner.symm (y, z)) := by
    apply outer.injective
    rw [outer.apply_symm_apply, houter]
    congr 1
    rw [← hinner, inner.symm_apply_apply]
  rw [hq]
  change polynomialFunctionRightTripleAlgEquiv G
      ((Algebra.TensorProduct.assoc k k k _ _ _)
        (Algebra.TensorProduct.map
          (coordinateComultiplication G)
          (.id k (Variety.PolynomialFunction G))
          (coordinateComultiplication G f))) _ =
    polynomialFunctionRightTripleAlgEquiv G
      (Algebra.TensorProduct.map
        (.id k (Variety.PolynomialFunction G))
        (coordinateComultiplication G)
        (coordinateComultiplication G f)) _
  rw [polynomialFunctionRightTripleAlgEquiv_assoc_map_left_apply,
    polynomialFunctionRightTripleAlgEquiv_map_right_apply,
    coordinateComultiplication_apply,
    coordinateComultiplication_apply, mul_assoc]

end

/-! Injectivity of tensor-square inclusions for subalgebras over a field. -/

section
open scoped TensorProduct

variable {k A : Type*} [Field k] [CommRing A] [Algebra k A]

lemma Subalgebra.tensorSquareInclusion_injective (C : Subalgebra k A) :
    Function.Injective (Algebra.TensorProduct.map C.val C.val) := by
  change Function.Injective
    (TensorProduct.map C.toSubmodule.subtype C.toSubmodule.subtype)
  exact TensorProduct.map_injective_of_flat_flat (R := k)
    _ _ C.toSubmodule.subtype_injective C.toSubmodule.subtype_injective

end

/-! Lifting algebra homomorphisms through injective algebra homomorphisms. -/

section

variable {k : Type*} [CommSemiring k]
variable {A B D : Type*}
  [Semiring A] [Algebra k A]
  [Semiring B] [Algebra k B]
  [Semiring D] [Algebra k D]

noncomputable def AlgHom.liftOfInjective
    (i : D →ₐ[k] B) (hi : Function.Injective i)
    (f : A →ₐ[k] B) (hf : ∀ a, f a ∈ i.range) : A →ₐ[k] D :=
  (AlgEquiv.ofInjective i hi).symm.toAlgHom.comp (f.codRestrict i.range hf)

lemma AlgHom.liftOfInjective_apply
    (i : D →ₐ[k] B) (hi : Function.Injective i)
    (f : A →ₐ[k] B) (hf : ∀ a, f a ∈ i.range) (a : A) :
    i (AlgHom.liftOfInjective i hi f hf a) = f a := by
  exact congrArg Subtype.val
    ((AlgEquiv.ofInjective i hi).apply_symm_apply (f.codRestrict i.range hf a))

end

/-! Restricting coordinate comultiplication to a tensor-stable subalgebra. -/

section
open scoped TensorProduct

variable {k : Type u} [Field k]

public noncomputable def coordinateSubalgebraComultiplication
    (G : Variety k) [AlgebraicGroup G]
    (C : Subalgebra k (Variety.PolynomialFunction G))
    (hcomul : ∀ q, q ∈ C → ∃ w : C ⊗[k] C,
      TensorProduct.map C.toSubmodule.subtype C.toSubmodule.subtype w =
        AlgebraicGroup.coordinateComultiplication G q) :
    C →ₐ[k] C ⊗[k] C :=
  AlgHom.liftOfInjective
    (Algebra.TensorProduct.map C.val C.val)
    (Subalgebra.tensorSquareInclusion_injective (k := k) C)
    ((AlgebraicGroup.coordinateComultiplication G).comp C.val)
    (fun (q : C) => by
      obtain ⟨w, hw⟩ := hcomul q.1 q.2
      exact ⟨w, hw⟩)

end

/-! The ambient computation formula for restricted coordinate comultiplication. -/

section
open scoped TensorProduct

variable {k : Type u} [Field k]

public lemma coordinateSubalgebraComultiplication_apply
    (G : Variety k) [AlgebraicGroup G]
    (C : Subalgebra k (Variety.PolynomialFunction G))
    (hcomul : ∀ q, q ∈ C → ∃ w : C ⊗[k] C,
      TensorProduct.map C.toSubmodule.subtype C.toSubmodule.subtype w =
        AlgebraicGroup.coordinateComultiplication G q)
    (q : C) :
    Algebra.TensorProduct.map C.val C.val
        (AlgebraicGroup.coordinateSubalgebraComultiplication G C hcomul q) =
      AlgebraicGroup.coordinateComultiplication G q.1 := by
  unfold AlgebraicGroup.coordinateSubalgebraComultiplication
  apply AlgHom.liftOfInjective_apply

end

/-! Coordinate counit restricted to a subalgebra. -/

section

variable {k : Type u} [Field k]

@[expose]
public noncomputable def coordinateSubalgebraCounit
    (G : Variety k) [AlgebraicGroup G]
    (C : Subalgebra k (Variety.PolynomialFunction G)) : C →ₐ[k] k :=
  (AlgebraicGroup.coordinateCounit G).comp C.val

/-! The computation formula for the restricted coordinate counit. -/

variable {k : Type u} [Field k]

public lemma coordinateSubalgebraCounit_apply
    (G : Variety k) [AlgebraicGroup G]
    (C : Subalgebra k (Variety.PolynomialFunction G)) (q : C) :
    AlgebraicGroup.coordinateSubalgebraCounit G C q =
      AlgebraicGroup.coordinateCounit G q.1 := rfl

end

/-! Coordinate antipode restricted to an antipode-stable subalgebra. -/

section

variable {k : Type u} [Field k]

@[expose]
public noncomputable def coordinateSubalgebraAntipode
    (G : Variety k) [AlgebraicGroup G]
    (C : Subalgebra k (Variety.PolynomialFunction G))
    (hantipode : ∀ q, q ∈ C → AlgebraicGroup.coordinateAntipode G q ∈ C) :
    C →ₐ[k] C :=
  ((AlgebraicGroup.coordinateAntipode G).comp C.val).codRestrict C
    (fun q => hantipode q.1 q.2)

end

/-! The ambient computation formula for the restricted coordinate antipode. -/

section

variable {k : Type u} [Field k]

public lemma coordinateSubalgebraAntipode_apply
    (G : Variety k) [AlgebraicGroup G]
    (C : Subalgebra k (Variety.PolynomialFunction G))
    (hantipode : ∀ q, q ∈ C → AlgebraicGroup.coordinateAntipode G q ∈ C)
    (q : C) :
    (AlgebraicGroup.coordinateSubalgebraAntipode G C hantipode q).1 =
      AlgebraicGroup.coordinateAntipode G q.1 := rfl

end

/-! Right-associated tensor-cube inclusion for a subalgebra. -/

section
open scoped TensorProduct

variable {k : Type u} [Field k]
variable {A : Type v} [CommRing A] [Algebra k A]

@[expose]
public noncomputable def Subalgebra.rightTripleInclusion (C : Subalgebra k A) :
    C ⊗[k] (C ⊗[k] C) →ₐ[k] A ⊗[k] (A ⊗[k] A) :=
  Algebra.TensorProduct.map C.val (Algebra.TensorProduct.map C.val C.val)

end

/-! Injectivity of the right-associated tensor-cube inclusion. -/

section
open scoped TensorProduct

variable {k : Type u} [Field k]
variable {A : Type v} [CommRing A] [Algebra k A]

public lemma Subalgebra.rightTripleInclusion_injective (C : Subalgebra k A) :
    Function.Injective (Subalgebra.rightTripleInclusion C) := by
  change Function.Injective
    (TensorProduct.map C.toSubmodule.subtype
      (Algebra.TensorProduct.map C.val C.val).toLinearMap)
  exact TensorProduct.map_injective_of_flat_flat (R := k)
    _ _ C.toSubmodule.subtype_injective
    (Subalgebra.tensorSquareInclusion_injective C)

end

/-! Coassociativity of coordinate comultiplication restricted to a stable subalgebra. -/

section
open scoped TensorProduct

variable {k : Type u} [Field k]

public lemma coordinateSubalgebraComultiplication_coassoc
    (G : Variety k) [AlgebraicGroup G]
    (C : Subalgebra k (Variety.PolynomialFunction G))
    (hcomul : ∀ q, q ∈ C → ∃ w : C ⊗[k] C,
      TensorProduct.map C.toSubmodule.subtype C.toSubmodule.subtype w =
        AlgebraicGroup.coordinateComultiplication G q) :
    (Algebra.TensorProduct.assoc k k k C C C).toAlgHom.comp
      ((Algebra.TensorProduct.map
        (AlgebraicGroup.coordinateSubalgebraComultiplication G C hcomul)
        (.id k C)).comp
        (AlgebraicGroup.coordinateSubalgebraComultiplication G C hcomul)) =
    (Algebra.TensorProduct.map
      (.id k C)
      (AlgebraicGroup.coordinateSubalgebraComultiplication G C hcomul)).comp
        (AlgebraicGroup.coordinateSubalgebraComultiplication G C hcomul) := by
  let A := Variety.PolynomialFunction G
  let i : C →ₐ[k] A := C.val
  let i2 : C ⊗[k] C →ₐ[k] A ⊗[k] A := Algebra.TensorProduct.map C.val C.val
  let i3 : C ⊗[k] (C ⊗[k] C) →ₐ[k] A ⊗[k] (A ⊗[k] A) :=
    Subalgebra.rightTripleInclusion C
  let dC : C →ₐ[k] C ⊗[k] C :=
    AlgebraicGroup.coordinateSubalgebraComultiplication G C hcomul
  let dA : A →ₐ[k] A ⊗[k] A := AlgebraicGroup.coordinateComultiplication G
  have hn : i2.comp dC = dA.comp i := by
    apply AlgHom.ext
    intro f
    exact AlgebraicGroup.coordinateSubalgebraComultiplication_apply G C hcomul f
  apply AlgHom.ext
  intro f
  apply Subalgebra.rightTripleInclusion_injective C
  change i3
      ((Algebra.TensorProduct.assoc k k k C C C)
        (Algebra.TensorProduct.map dC (.id k C) (dC f))) =
    i3 (Algebra.TensorProduct.map (.id k C) dC (dC f))
  change TensorProduct.map i.toLinearMap
      (TensorProduct.map i.toLinearMap i.toLinearMap)
      ((TensorProduct.assoc k C C C)
        (TensorProduct.map dC.toLinearMap LinearMap.id (dC f))) =
    TensorProduct.map i.toLinearMap
      (TensorProduct.map i.toLinearMap i.toLinearMap)
      (TensorProduct.map LinearMap.id dC.toLinearMap (dC f))
  rw [TensorProduct.map_map_assoc]
  have hnlin : i2.toLinearMap ∘ₗ dC.toLinearMap = dA.toLinearMap ∘ₗ i.toLinearMap := by
    exact congrArg AlgHom.toLinearMap hn
  have hf : i2 (dC f) = dA (i f) := by
    have := congrArg (fun F : C →ₐ[k] A ⊗[k] A => F f) hn
    simpa only [AlgHom.comp_apply] using this
  calc
    (TensorProduct.assoc k A A A)
        (TensorProduct.map i2.toLinearMap i.toLinearMap
          (TensorProduct.map dC.toLinearMap LinearMap.id (dC f))) =
      (TensorProduct.assoc k A A A)
        (TensorProduct.map (i2.toLinearMap ∘ₗ dC.toLinearMap)
          (i.toLinearMap ∘ₗ LinearMap.id) (dC f)) := by
            rw [TensorProduct.map_map]
    _ = (TensorProduct.assoc k A A A)
        (TensorProduct.map (dA.toLinearMap ∘ₗ i.toLinearMap)
          i.toLinearMap (dC f)) := by rw [hnlin]; rfl
    _ = (TensorProduct.assoc k A A A)
        (TensorProduct.map dA.toLinearMap LinearMap.id
          (TensorProduct.map i.toLinearMap i.toLinearMap (dC f))) := by
          rw [TensorProduct.map_map]
          rfl
    _ = (TensorProduct.assoc k A A A)
        (TensorProduct.map dA.toLinearMap LinearMap.id (i2 (dC f))) := rfl
    _ = (TensorProduct.assoc k A A A)
        (TensorProduct.map dA.toLinearMap LinearMap.id (dA (i f))) := by rw [hf]
    _ = TensorProduct.map LinearMap.id dA.toLinearMap (dA (i f)) := by
      have hcolin := congrArg AlgHom.toLinearMap
        (AlgebraicGroup.coordinateComultiplication_coassoc G)
      exact LinearMap.congr_fun hcolin (i f)
    _ = TensorProduct.map LinearMap.id dA.toLinearMap (i2 (dC f)) := by rw [hf]
    _ = TensorProduct.map LinearMap.id dA.toLinearMap
        (TensorProduct.map i.toLinearMap i.toLinearMap (dC f)) := rfl
    _ = TensorProduct.map i.toLinearMap
        (dA.toLinearMap ∘ₗ i.toLinearMap) (dC f) := by
      rw [TensorProduct.map_map]
      rfl
    _ = TensorProduct.map i.toLinearMap
        (i2.toLinearMap ∘ₗ dC.toLinearMap) (dC f) := by rw [hnlin]
    _ = TensorProduct.map i.toLinearMap i2.toLinearMap
        (TensorProduct.map LinearMap.id dC.toLinearMap (dC f)) := by
      rw [TensorProduct.map_map]
      rfl

end

/-! The left counit law for restricted coordinate comultiplication. -/

section
open scoped TensorProduct

variable {k : Type u} [Field k]

public lemma coordinateSubalgebraComultiplication_counit_left
    (G : Variety k) [AlgebraicGroup G]
    (C : Subalgebra k (Variety.PolynomialFunction G))
    (hcomul : ∀ q, q ∈ C → ∃ w : C ⊗[k] C,
      TensorProduct.map C.toSubmodule.subtype C.toSubmodule.subtype w =
        AlgebraicGroup.coordinateComultiplication G q) :
    (Algebra.TensorProduct.map
      (AlgebraicGroup.coordinateSubalgebraCounit G C)
      (.id k C)).comp
        (AlgebraicGroup.coordinateSubalgebraComultiplication G C hcomul) =
      (Algebra.TensorProduct.lid k C).symm := by
  apply AlgHom.ext
  intro f
  apply (Algebra.TensorProduct.lid k C).injective
  apply Subtype.ext
  apply Variety.PolynomialFunction.ext
  intro x
  rw [AlgHom.comp_apply]
  let t := AlgebraicGroup.coordinateSubalgebraComultiplication G C hcomul f
  have ht :
      ((Algebra.TensorProduct.lid k C)
        (Algebra.TensorProduct.map
          (AlgebraicGroup.coordinateSubalgebraCounit G C)
          (.id k C) t)).val x =
        polynomialFunctionTensor G G
          (Algebra.TensorProduct.map C.val C.val t)
          ((Variety.prodPointEquiv G G).symm (1, x)) := by
    induction t using TensorProduct.induction_on with
    | zero => simp
    | add a b ha hb =>
        rw [map_add, map_add, map_add, map_add]
        simpa [Variety.PolynomialFunction.toFun] using congrArg₂ (· + ·) ha hb
    | tmul a b =>
        rw [Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.lid_tmul]
        change _ = polynomialFunctionTensor G G
          (Algebra.TensorProduct.map C.val C.val (a ⊗ₜ[k] b)) _
        rw [Algebra.TensorProduct.map_tmul, polynomialFunctionTensor_tmul,
          AlgebraicGroup.coordinateSubalgebraCounit_apply]
        simp [polynomialFunction_mul_apply, polynomialFunctionLeft_apply,
          polynomialFunctionRight_apply, polynomialFunction_smul_apply]
  calc
    ((Algebra.TensorProduct.lid k C)
        (Algebra.TensorProduct.map
          (AlgebraicGroup.coordinateSubalgebraCounit G C)
          (.id k C) t)).val x =
      polynomialFunctionTensor G G
        (Algebra.TensorProduct.map C.val C.val t)
        ((Variety.prodPointEquiv G G).symm (1, x)) := ht
    _ = polynomialFunctionTensor G G
        (AlgebraicGroup.coordinateComultiplication G f.val)
        ((Variety.prodPointEquiv G G).symm (1, x)) := by
      rw [AlgebraicGroup.coordinateSubalgebraComultiplication_apply G C hcomul f]
    _ = f.val (1 * x) := AlgebraicGroup.coordinateComultiplication_apply G f.val 1 x
    _ = f.val x := by rw [one_mul]
    _ = ((Algebra.TensorProduct.lid k C)
        ((Algebra.TensorProduct.lid k C).symm f)).val x := by
      exact congrArg (fun g : C => g.val x)
        ((Algebra.TensorProduct.lid k C).apply_symm_apply f).symm

end

/-! The right counit law for restricted coordinate comultiplication. -/

section
open scoped TensorProduct

variable {k : Type u} [Field k]

public lemma coordinateSubalgebraComultiplication_counit_right
    (G : Variety k) [AlgebraicGroup G]
    (C : Subalgebra k (Variety.PolynomialFunction G))
    (hcomul : ∀ q, q ∈ C → ∃ w : C ⊗[k] C,
      TensorProduct.map C.toSubmodule.subtype C.toSubmodule.subtype w =
        AlgebraicGroup.coordinateComultiplication G q) :
    (Algebra.TensorProduct.map
      (.id k C)
      (AlgebraicGroup.coordinateSubalgebraCounit G C)).comp
        (AlgebraicGroup.coordinateSubalgebraComultiplication G C hcomul) =
      (Algebra.TensorProduct.rid k k C).symm := by
  apply AlgHom.ext
  intro f
  apply (Algebra.TensorProduct.rid k k C).injective
  apply Subtype.ext
  apply Variety.PolynomialFunction.ext
  intro x
  rw [AlgHom.comp_apply]
  let t := AlgebraicGroup.coordinateSubalgebraComultiplication G C hcomul f
  have ht :
      ((Algebra.TensorProduct.rid k k C)
        (Algebra.TensorProduct.map
          (.id k C)
          (AlgebraicGroup.coordinateSubalgebraCounit G C) t)).val x =
        polynomialFunctionTensor G G
          (Algebra.TensorProduct.map C.val C.val t)
          ((Variety.prodPointEquiv G G).symm (x, 1)) := by
    induction t using TensorProduct.induction_on with
    | zero => simp
    | add a b ha hb =>
        rw [map_add, map_add, map_add, map_add]
        simpa [Variety.PolynomialFunction.toFun] using congrArg₂ (· + ·) ha hb
    | tmul a b =>
        rw [Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.rid_tmul]
        change _ = polynomialFunctionTensor G G
          (Algebra.TensorProduct.map C.val C.val (a ⊗ₜ[k] b)) _
        rw [Algebra.TensorProduct.map_tmul, polynomialFunctionTensor_tmul,
          AlgebraicGroup.coordinateSubalgebraCounit_apply,
          AlgebraicGroup.coordinateCounit_apply]
        simp only [polynomialFunction_mul_apply, polynomialFunctionLeft_apply,
          polynomialFunctionRight_apply, Equiv.apply_symm_apply, AlgHom.id_apply]
        rw [show ((b.val 1 • a : C).val) = b.val 1 • a.val by rfl,
          polynomialFunction_smul_apply]
        exact mul_comm _ _
  calc
    ((Algebra.TensorProduct.rid k k C)
        (Algebra.TensorProduct.map
          (.id k C)
          (AlgebraicGroup.coordinateSubalgebraCounit G C) t)).val x =
      polynomialFunctionTensor G G
        (Algebra.TensorProduct.map C.val C.val t)
        ((Variety.prodPointEquiv G G).symm (x, 1)) := ht
    _ = polynomialFunctionTensor G G
        (AlgebraicGroup.coordinateComultiplication G f.val)
        ((Variety.prodPointEquiv G G).symm (x, 1)) := by
      rw [AlgebraicGroup.coordinateSubalgebraComultiplication_apply G C hcomul f]
    _ = f.val (x * 1) := AlgebraicGroup.coordinateComultiplication_apply G f.val x 1
    _ = f.val x := by rw [mul_one]
    _ = ((Algebra.TensorProduct.rid k k C)
        ((Algebra.TensorProduct.rid k k C).symm f)).val x := by
      exact congrArg (fun g : C => g.val x)
        ((Algebra.TensorProduct.rid k k C).apply_symm_apply f).symm

end

/-! A bialgebra structure on a comultiplication-stable coordinate subalgebra. -/

section
open scoped TensorProduct

variable {k : Type u} [Field k]

/-- The coordinate bialgebra structure restricted to a subalgebra stable under
coordinate comultiplication. -/
@[expose, implicit_reducible]
public noncomputable def coordinateSubalgebraBialgebra
    (G : Variety k) [AlgebraicGroup G]
    (C : Subalgebra k (Variety.PolynomialFunction G))
    (hcomul : ∀ q, q ∈ C → ∃ w : C ⊗[k] C,
      TensorProduct.map C.toSubmodule.subtype C.toSubmodule.subtype w =
        AlgebraicGroup.coordinateComultiplication G q) :
    Bialgebra k C :=
  Bialgebra.ofAlgHom
    (AlgebraicGroup.coordinateSubalgebraComultiplication G C hcomul)
    (AlgebraicGroup.coordinateSubalgebraCounit G C)
    (AlgebraicGroup.coordinateSubalgebraComultiplication_coassoc G C hcomul)
    (AlgebraicGroup.coordinateSubalgebraComultiplication_counit_left G C hcomul)
    (AlgebraicGroup.coordinateSubalgebraComultiplication_counit_right G C hcomul)

end

/-! The left antipode identity on a stable coordinate subalgebra. -/

section
open scoped TensorProduct
variable {k : Type u} [Field k]

public lemma coordinateSubalgebraAntipode_mul_left
    (G : Variety k) [AlgebraicGroup G]
    (C : Subalgebra k (Variety.PolynomialFunction G))
    (hcomul : ∀ q, q ∈ C → ∃ w : C ⊗[k] C,
      TensorProduct.map C.toSubmodule.subtype C.toSubmodule.subtype w =
        AlgebraicGroup.coordinateComultiplication G q)
    (hantipode : ∀ q, q ∈ C → AlgebraicGroup.coordinateAntipode G q ∈ C) :
    ((Algebra.TensorProduct.lift
      (AlgebraicGroup.coordinateSubalgebraAntipode G C hantipode)
      (.id k C)
      (fun _ _ => Commute.all _ _)).comp
        (AlgebraicGroup.coordinateSubalgebraComultiplication G C hcomul)) =
      (Algebra.ofId k C).comp
        (AlgebraicGroup.coordinateSubalgebraCounit G C) := by
  apply AlgHom.ext
  intro f
  apply Subtype.ext
  apply Variety.PolynomialFunction.ext
  intro x
  rw [AlgHom.comp_apply, AlgHom.comp_apply]
  let t := AlgebraicGroup.coordinateSubalgebraComultiplication G C hcomul f
  have ht :
      (Algebra.TensorProduct.lift
          (AlgebraicGroup.coordinateSubalgebraAntipode G C hantipode)
          (.id k C) (fun _ _ => Commute.all _ _) t).val x =
        polynomialFunctionTensor G G
          (Algebra.TensorProduct.map C.val C.val t)
          ((Variety.prodPointEquiv G G).symm (x⁻¹, x)) := by
    induction t using TensorProduct.induction_on with
    | zero => simp
    | add a b ha hb =>
        rw [map_add, map_add, map_add]
        simpa [Variety.PolynomialFunction.toFun] using congrArg₂ (· + ·) ha hb
    | tmul a b =>
        rw [Algebra.TensorProduct.lift_tmul]
        change ((AlgebraicGroup.coordinateSubalgebraAntipode G C hantipode a) * b).val x =
          polynomialFunctionTensor G G
            (Algebra.TensorProduct.map C.val C.val (a ⊗ₜ[k] b)) _
        rw [Algebra.TensorProduct.map_tmul, polynomialFunctionTensor_tmul]
        have ha := AlgebraicGroup.coordinateSubalgebraAntipode_apply G C hantipode a
        change (AlgebraicGroup.coordinateSubalgebraAntipode G C hantipode a).val = _ at ha
        change ((AlgebraicGroup.coordinateSubalgebraAntipode G C hantipode a).val * b.val) x = _
        rw [ha]
        simp [polynomialFunction_mul_apply, polynomialFunctionLeft_apply,
          polynomialFunctionRight_apply, AlgebraicGroup.coordinateAntipode_apply]
  have hcompat :=
    AlgebraicGroup.coordinateSubalgebraComultiplication_apply G C hcomul f
  change Algebra.TensorProduct.map C.val C.val t =
    AlgebraicGroup.coordinateComultiplication G f.val at hcompat
  calc
    (Algebra.TensorProduct.lift
        (AlgebraicGroup.coordinateSubalgebraAntipode G C hantipode)
        (.id k C) (fun _ _ => Commute.all _ _) t).val x =
      polynomialFunctionTensor G G
        (Algebra.TensorProduct.map C.val C.val t)
        ((Variety.prodPointEquiv G G).symm (x⁻¹, x)) := ht
    _ = polynomialFunctionTensor G G
        (AlgebraicGroup.coordinateComultiplication G f.val)
        ((Variety.prodPointEquiv G G).symm (x⁻¹, x)) := by rw [hcompat]
    _ = f.val (x⁻¹ * x) := AlgebraicGroup.coordinateComultiplication_apply G f.val x⁻¹ x
    _ = f.val 1 := by rw [inv_mul_cancel]
    _ = (algebraMap k C (AlgebraicGroup.coordinateSubalgebraCounit G C f)).val x := by
      rw [AlgebraicGroup.coordinateSubalgebraCounit_apply]
      exact polynomialFunction_algebraMap_apply G (f.val 1) x |>.symm

end

/-! The right antipode identity on a stable coordinate subalgebra. -/

section
open scoped TensorProduct
variable {k : Type u} [Field k]

public lemma coordinateSubalgebraAntipode_mul_right
    (G : Variety k) [AlgebraicGroup G]
    (C : Subalgebra k (Variety.PolynomialFunction G))
    (hcomul : ∀ q, q ∈ C → ∃ w : C ⊗[k] C,
      TensorProduct.map C.toSubmodule.subtype C.toSubmodule.subtype w =
        AlgebraicGroup.coordinateComultiplication G q)
    (hantipode : ∀ q, q ∈ C → AlgebraicGroup.coordinateAntipode G q ∈ C) :
    ((Algebra.TensorProduct.lift
      (.id k C)
      (AlgebraicGroup.coordinateSubalgebraAntipode G C hantipode)
      (fun _ _ => Commute.all _ _)).comp
        (AlgebraicGroup.coordinateSubalgebraComultiplication G C hcomul)) =
      (Algebra.ofId k C).comp
        (AlgebraicGroup.coordinateSubalgebraCounit G C) := by
  apply AlgHom.ext
  intro f
  apply Subtype.ext
  apply Variety.PolynomialFunction.ext
  intro x
  rw [AlgHom.comp_apply, AlgHom.comp_apply]
  let t := AlgebraicGroup.coordinateSubalgebraComultiplication G C hcomul f
  have ht :
      (Algebra.TensorProduct.lift
          (.id k C)
          (AlgebraicGroup.coordinateSubalgebraAntipode G C hantipode)
          (fun _ _ => Commute.all _ _) t).val x =
        polynomialFunctionTensor G G
          (Algebra.TensorProduct.map C.val C.val t)
          ((Variety.prodPointEquiv G G).symm (x, x⁻¹)) := by
    induction t using TensorProduct.induction_on with
    | zero => simp
    | add a b ha hb =>
        rw [map_add, map_add, map_add]
        simpa [Variety.PolynomialFunction.toFun] using congrArg₂ (· + ·) ha hb
    | tmul a b =>
        rw [Algebra.TensorProduct.lift_tmul]
        change (a * (AlgebraicGroup.coordinateSubalgebraAntipode G C hantipode b)).val x =
          polynomialFunctionTensor G G
            (Algebra.TensorProduct.map C.val C.val (a ⊗ₜ[k] b)) _
        rw [Algebra.TensorProduct.map_tmul, polynomialFunctionTensor_tmul]
        have hb := AlgebraicGroup.coordinateSubalgebraAntipode_apply G C hantipode b
        change (AlgebraicGroup.coordinateSubalgebraAntipode G C hantipode b).val = _ at hb
        change (a.val * (AlgebraicGroup.coordinateSubalgebraAntipode G C hantipode b).val) x = _
        rw [hb]
        simp [polynomialFunction_mul_apply, polynomialFunctionLeft_apply,
          polynomialFunctionRight_apply, AlgebraicGroup.coordinateAntipode_apply]
  have hcompat :=
    AlgebraicGroup.coordinateSubalgebraComultiplication_apply G C hcomul f
  change Algebra.TensorProduct.map C.val C.val t =
    AlgebraicGroup.coordinateComultiplication G f.val at hcompat
  calc
    (Algebra.TensorProduct.lift
        (.id k C)
        (AlgebraicGroup.coordinateSubalgebraAntipode G C hantipode)
        (fun _ _ => Commute.all _ _) t).val x =
      polynomialFunctionTensor G G
        (Algebra.TensorProduct.map C.val C.val t)
        ((Variety.prodPointEquiv G G).symm (x, x⁻¹)) := ht
    _ = polynomialFunctionTensor G G
        (AlgebraicGroup.coordinateComultiplication G f.val)
        ((Variety.prodPointEquiv G G).symm (x, x⁻¹)) := by rw [hcompat]
    _ = f.val (x * x⁻¹) := AlgebraicGroup.coordinateComultiplication_apply G f.val x x⁻¹
    _ = f.val 1 := by rw [mul_inv_cancel]
    _ = (algebraMap k C (AlgebraicGroup.coordinateSubalgebraCounit G C f)).val x := by
      rw [AlgebraicGroup.coordinateSubalgebraCounit_apply]
      exact polynomialFunction_algebraMap_apply G (f.val 1) x |>.symm

end

/-! A Hopf algebra structure on a stable coordinate subalgebra. -/

section
open scoped TensorProduct

variable {k : Type u} [Field k]

/-- The coordinate Hopf algebra structure restricted to a subalgebra stable
under coordinate comultiplication and antipode. -/
@[expose, implicit_reducible]
public noncomputable def coordinateSubalgebraHopfAlgebra
    (G : Variety k) [AlgebraicGroup G]
    (C : Subalgebra k (Variety.PolynomialFunction G))
    (hcomul : ∀ q, q ∈ C → ∃ w : C ⊗[k] C,
      TensorProduct.map C.toSubmodule.subtype C.toSubmodule.subtype w =
        AlgebraicGroup.coordinateComultiplication G q)
    (hantipode : ∀ q, q ∈ C → AlgebraicGroup.coordinateAntipode G q ∈ C) :
    HopfAlgebra k C := by
  letI : Bialgebra k C :=
    AlgebraicGroup.coordinateSubalgebraBialgebra G C hcomul
  exact HopfAlgebra.ofAlgHom
    (AlgebraicGroup.coordinateSubalgebraAntipode G C hantipode)
    (AlgebraicGroup.coordinateSubalgebraAntipode_mul_left G C hcomul hantipode)
    (AlgebraicGroup.coordinateSubalgebraAntipode_mul_right G C hcomul hantipode)

end

end Theory.AlgebraicGroup

