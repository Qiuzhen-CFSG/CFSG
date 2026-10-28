module

public import Theory.AlgebraicGroup.ClosedSubgroup.Invariant
public import Theory.AlgebraicGroup.CoordinateRing.Hopf.Basic

universe u v

/-! The coordinate Hopf algebra of normal right-invariant functions. -/

namespace Theory.AlgebraicGroup

section

variable {k : Type u} [Field k]

@[expose]
public noncomputable def rightInvariantCoordinateAntipode
    {G : Variety k} [AlgebraicGroup G] (H : ClosedSubgroup G)
    (hN : H.toSubgroup.Normal) :
    AlgebraicGroup.rightInvariantCoordinateRing H →ₐ[k]
      AlgebraicGroup.rightInvariantCoordinateRing H where
  toFun := fun f =>
    ⟨AlgebraicGroup.coordinateAntipode G f.val,
      AlgebraicGroup.coordinateAntipode_mem_rightInvariantCoordinateRing
        H hN f.val f.property⟩
  map_one' := Subtype.ext (map_one (AlgebraicGroup.coordinateAntipode G))
  map_mul' := fun f g => Subtype.ext
    (map_mul (AlgebraicGroup.coordinateAntipode G) f.val g.val)
  map_zero' := Subtype.ext (map_zero (AlgebraicGroup.coordinateAntipode G))
  map_add' := fun f g => Subtype.ext
    (map_add (AlgebraicGroup.coordinateAntipode G) f.val g.val)
  commutes' := fun r => Subtype.ext
    ((AlgebraicGroup.coordinateAntipode G).commutes r)

end

/-! Ambient compatibility of the descended invariant antipode. -/

section
variable {k : Type u} [Field k]

public lemma rightInvariantCoordinateAntipode_apply
    {G : Variety k} [AlgebraicGroup G] (H : ClosedSubgroup G)
    (hN : H.toSubgroup.Normal)
    (f : AlgebraicGroup.rightInvariantCoordinateRing H) :
    (AlgebraicGroup.rightInvariantCoordinateAntipode H hN f).val =
      AlgebraicGroup.coordinateAntipode G f.val := rfl

end

/-! Pointwise normal right-invariance of coordinate comultiplication. -/

section
open scoped TensorProduct
variable {k : Type u} [Field k]

public lemma coordinateComultiplication_apply_rightInvariant
    {G : Variety k} [AlgebraicGroup G] (H : ClosedSubgroup G)
    (hN : H.toSubgroup.Normal) (f : Variety.PolynomialFunction G)
    (hf : f ∈ AlgebraicGroup.rightInvariantCoordinateRing H)
    (g₁ g₂ h₁ h₂ : Variety.Point G)
    (hh₁ : h₁ ∈ H.toSubgroup) (hh₂ : h₂ ∈ H.toSubgroup) :
    polynomialFunctionTensor G G (AlgebraicGroup.coordinateComultiplication G f)
        ((Variety.prodPointEquiv G G).symm (g₁ * h₁, g₂ * h₂)) =
      polynomialFunctionTensor G G (AlgebraicGroup.coordinateComultiplication G f)
        ((Variety.prodPointEquiv G G).symm (g₁, g₂)) := by
  rw [AlgebraicGroup.coordinateComultiplication_apply,
    AlgebraicGroup.coordinateComultiplication_apply]
  rw [AlgebraicGroup.mem_rightInvariantCoordinateRing_iff] at hf
  have hconj : g₂⁻¹ * h₁ * g₂ ∈ H.toSubgroup := hN.conj_mem' h₁ hh₁ g₂
  have hprod : (g₂⁻¹ * h₁ * g₂) * h₂ ∈ H.toSubgroup :=
    H.toSubgroup.mul_mem hconj hh₂
  calc
    f ((g₁ * h₁) * (g₂ * h₂)) =
        f ((g₁ * g₂) * ((g₂⁻¹ * h₁ * g₂) * h₂)) := by
      congr 1
      simp [mul_assoc]
    _ = f (g₁ * g₂) := hf (g₁ * g₂) _ hprod

end

/-! Factoring a product polynomial through right-invariant functions in its second variable. -/

section
open scoped TensorProduct
variable {k : Type u} [Field k]

public lemma exists_tensor_rightInvariant_of_eval_rightInvariant
    {G : Variety k} [AlgebraicGroup G] (H : ClosedSubgroup G)
    (z : Variety.PolynomialFunction G ⊗[k] Variety.PolynomialFunction G)
    (hz : ∀ (x y h : Variety.Point G), h ∈ H.toSubgroup →
      polynomialFunctionTensor G G z
          ((Variety.prodPointEquiv G G).symm (x, y * h)) =
        polynomialFunctionTensor G G z
          ((Variety.prodPointEquiv G G).symm (x, y))) :
    ∃ w : Variety.PolynomialFunction G ⊗[k]
        AlgebraicGroup.rightInvariantCoordinateRing H,
      TensorProduct.map LinearMap.id
        (AlgebraicGroup.rightInvariantCoordinateRing H).toSubmodule.subtype w = z := by
  let B := AlgebraicGroup.rightInvariantCoordinateRing H
  let b := Module.Free.chooseBasis k (Variety.PolynomialFunction G)
  obtain ⟨c, hc⟩ := TensorProduct.eq_repr_basis_left b z
  have hcoeff : ∀ i, c i ∈ B := by
    intro i
    rw [AlgebraicGroup.mem_rightInvariantCoordinateRing_iff]
    intro y h hh
    let q : Variety.PolynomialFunction G :=
      c.sum (fun j g => (g (y * h) - g y) • b j)
    have hq : q = 0 := by
      apply Variety.PolynomialFunction.ext
      intro x
      have heq := hz x y h hh
      rw [← hc] at heq
      change polynomialFunctionEvalAddHom (Variety.prod G G)
          ((Variety.prodPointEquiv G G).symm (x, y * h))
          (polynomialFunctionTensor G G (c.sum fun j g => b j ⊗ₜ[k] g)) =
        polynomialFunctionEvalAddHom (Variety.prod G G)
          ((Variety.prodPointEquiv G G).symm (x, y))
          (polynomialFunctionTensor G G (c.sum fun j g => b j ⊗ₜ[k] g)) at heq
      have heq' :
          c.sum (fun j g => b j x * g (y * h)) =
            c.sum (fun j g => b j x * g y) := by
        simpa only [map_finsuppSum, Finsupp.sum_apply,
          polynomialFunctionTensor_tmul, map_mul,
          polynomialFunctionEvalAddHom_apply, polynomialFunctionLeft_apply,
          polynomialFunctionRight_apply, polynomialFunction_mul_apply,
          Equiv.apply_symm_apply] using heq
      have hqeval := map_finsuppSum (polynomialFunctionEvalAddHom G x) c
        (fun j g => (g (y * h) - g y) • b j)
      change (polynomialFunctionEvalAddHom G x)
        (c.sum (fun j g => (g (y * h) - g y) • b j)) = 0
      rw [hqeval]
      calc
        c.sum (fun j g => (polynomialFunctionEvalAddHom G x)
            ((g (y * h) - g y) • b j)) =
            c.sum (fun j g => b j x * g (y * h) - b j x * g y) := by
          apply Finsupp.sum_congr
          intro j hj
          rw [polynomialFunctionEvalAddHom_apply,
            polynomialFunction_smul_apply]
          ring
        _ = c.sum (fun j g => b j x * g (y * h)) -
            c.sum (fun j g => b j x * g y) := Finsupp.sum_sub
        _ = 0 := sub_eq_zero.mpr heq'
    have hrepr := congrArg
      (fun f : Variety.PolynomialFunction G => b.repr f i) hq
    by_cases hci : c i = 0
    · rw [hci]
      rfl
    · have hi_mem : i ∈ c.support := Finsupp.mem_support_iff.mpr hci
      have hi : c i (y * h) - c i y = 0 := by
        simpa [q, map_finsuppSum, Finsupp.sum, Finsupp.single_apply, hi_mem] using hrepr
      exact sub_eq_zero.mp hi
  let w : Variety.PolynomialFunction G ⊗[k] B :=
    ∑ i ∈ c.support, b i ⊗ₜ[k] (⟨c i, hcoeff i⟩ : B)
  refine ⟨w, ?_⟩
  rw [← hc]
  simp [w, Finsupp.sum]

end

/-! Factoring a product polynomial through right-invariant functions in its first variable. -/

section
open scoped TensorProduct
variable {k : Type u} [Field k]

public lemma exists_tensor_rightInvariant_rightInvariant_of_eval_leftInvariant
    {G : Variety k} [AlgebraicGroup G] (H : ClosedSubgroup G)
    (w : Variety.PolynomialFunction G ⊗[k]
      AlgebraicGroup.rightInvariantCoordinateRing H)
    (hz : ∀ (x y h : Variety.Point G), h ∈ H.toSubgroup →
      polynomialFunctionTensor G G
          (TensorProduct.map LinearMap.id
            (AlgebraicGroup.rightInvariantCoordinateRing H).toSubmodule.subtype w)
          ((Variety.prodPointEquiv G G).symm (x * h, y)) =
        polynomialFunctionTensor G G
          (TensorProduct.map LinearMap.id
            (AlgebraicGroup.rightInvariantCoordinateRing H).toSubmodule.subtype w)
          ((Variety.prodPointEquiv G G).symm (x, y))) :
    ∃ v : AlgebraicGroup.rightInvariantCoordinateRing H ⊗[k]
        AlgebraicGroup.rightInvariantCoordinateRing H,
      TensorProduct.map
        (AlgebraicGroup.rightInvariantCoordinateRing H).toSubmodule.subtype
        (AlgebraicGroup.rightInvariantCoordinateRing H).toSubmodule.subtype v =
      TensorProduct.map LinearMap.id
        (AlgebraicGroup.rightInvariantCoordinateRing H).toSubmodule.subtype w := by
  let B := AlgebraicGroup.rightInvariantCoordinateRing H
  let b := Module.Free.chooseBasis k B
  obtain ⟨c, hc⟩ := TensorProduct.eq_repr_basis_right b w
  have hcoeff : ∀ i, c i ∈ B := by
    intro i
    rw [AlgebraicGroup.mem_rightInvariantCoordinateRing_iff]
    intro x h hh
    let q : B := c.sum (fun j f => (f (x * h) - f x) • b j)
    have hq : q = 0 := by
      apply Subtype.ext
      apply Variety.PolynomialFunction.ext
      intro y
      have heq := hz x y h hh
      rw [← hc] at heq
      change polynomialFunctionEvalAddHom (Variety.prod G G)
          ((Variety.prodPointEquiv G G).symm (x * h, y))
          (polynomialFunctionTensor G G
            (TensorProduct.map LinearMap.id B.toSubmodule.subtype
              (c.sum fun j f => f ⊗ₜ[k] b j))) =
        polynomialFunctionEvalAddHom (Variety.prod G G)
          ((Variety.prodPointEquiv G G).symm (x, y))
          (polynomialFunctionTensor G G
            (TensorProduct.map LinearMap.id B.toSubmodule.subtype
              (c.sum fun j f => f ⊗ₜ[k] b j))) at heq
      have heq' :
          c.sum (fun j f => f (x * h) * (b j : B).val y) =
            c.sum (fun j f => f x * (b j : B).val y) := by
        simpa only [map_finsuppSum, Finsupp.sum_apply, TensorProduct.map_tmul,
          LinearMap.id_coe, id_eq, Submodule.coe_subtype,
          polynomialFunctionTensor_tmul, map_mul,
          polynomialFunctionEvalAddHom_apply, polynomialFunctionLeft_apply,
          polynomialFunctionRight_apply, polynomialFunction_mul_apply,
          Equiv.apply_symm_apply] using heq
      have hsub := map_finsuppSum B.toSubmodule.subtype c
        (fun j f => (f (x * h) - f x) • b j)
      change (B.toSubmodule.subtype
        (c.sum fun j f => (f (x * h) - f x) • b j)) y = 0
      rw [hsub]
      change (polynomialFunctionEvalAddHom G y)
        (c.sum fun j f => B.toSubmodule.subtype
          ((f (x * h) - f x) • b j)) = 0
      rw [map_finsuppSum]
      calc
        c.sum (fun j f => (B.toSubmodule.subtype
            ((f (x * h) - f x) • b j)) y) =
            c.sum (fun j f => f (x * h) * (b j : B).val y -
              f x * (b j : B).val y) := by
          apply Finsupp.sum_congr
          intro j hj
          rw [show (B.toSubmodule.subtype
            ((c j (x * h) - c j x) • b j)) y =
              (c j (x * h) - c j x) * (b j : B).val y by
            change (((c j (x * h) - c j x) • b j : B) :
              Variety.PolynomialFunction G) y = _
            exact polynomialFunction_smul_apply G _ (b j).val y]
          ring
        _ = c.sum (fun j f => f (x * h) * (b j : B).val y) -
            c.sum (fun j f => f x * (b j : B).val y) := Finsupp.sum_sub
        _ = 0 := sub_eq_zero.mpr heq'
    have hrepr := congrArg (fun f : B => b.repr f i) hq
    by_cases hci : c i = 0
    · rw [hci]
      rfl
    · have hi_mem : i ∈ c.support := Finsupp.mem_support_iff.mpr hci
      have hi : c i (x * h) - c i x = 0 := by
        simpa [q, map_finsuppSum, Finsupp.sum, Finsupp.single_apply, hi_mem] using hrepr
      exact sub_eq_zero.mp hi
  let v : B ⊗[k] B :=
    ∑ i ∈ c.support, (⟨c i, hcoeff i⟩ : B) ⊗ₜ[k] b i
  refine ⟨v, ?_⟩
  rw [← hc]
  simp [v, Finsupp.sum]

end

/-! Normal right-invariants have comultiplication in the tensor square of invariants. -/

section
open scoped TensorProduct
variable {k : Type u} [Field k]

public lemma exists_rightInvariantTensor_comultiplication
    {G : Variety k} [AlgebraicGroup G] (H : ClosedSubgroup G)
    (hN : H.toSubgroup.Normal) (f : Variety.PolynomialFunction G)
    (hf : f ∈ AlgebraicGroup.rightInvariantCoordinateRing H) :
    ∃ z : AlgebraicGroup.rightInvariantCoordinateRing H ⊗[k]
        AlgebraicGroup.rightInvariantCoordinateRing H,
      TensorProduct.map
        (AlgebraicGroup.rightInvariantCoordinateRing H).toSubmodule.subtype
        (AlgebraicGroup.rightInvariantCoordinateRing H).toSubmodule.subtype z =
      AlgebraicGroup.coordinateComultiplication G f := by
  let Δf := AlgebraicGroup.coordinateComultiplication G f
  obtain ⟨w, hw⟩ :=
    AlgebraicGroup.exists_tensor_rightInvariant_of_eval_rightInvariant H Δf (by
      intro x y h hh
      simpa [Δf] using
        AlgebraicGroup.coordinateComultiplication_apply_rightInvariant
          H hN f hf x y 1 h H.toSubgroup.one_mem hh)
  obtain ⟨z, hz⟩ :=
    AlgebraicGroup.exists_tensor_rightInvariant_rightInvariant_of_eval_leftInvariant H w (by
      intro x y h hh
      rw [hw]
      simpa [Δf] using
        AlgebraicGroup.coordinateComultiplication_apply_rightInvariant
          H hN f hf x y h 1 hh H.toSubgroup.one_mem)
  exact ⟨z, hz.trans hw⟩

end

/-! The coordinate comultiplication descended to normal right-invariants. -/

section
open scoped TensorProduct
variable {k : Type u} [Field k]

@[expose]
public noncomputable def rightInvariantCoordinateComultiplication
    {G : Variety k} [AlgebraicGroup G] (H : ClosedSubgroup G)
    (hN : H.toSubgroup.Normal) :
    AlgebraicGroup.rightInvariantCoordinateRing H →ₐ[k]
      AlgebraicGroup.rightInvariantCoordinateRing H ⊗[k]
        AlgebraicGroup.rightInvariantCoordinateRing H := by
  let B := AlgebraicGroup.rightInvariantCoordinateRing H
  let A := Variety.PolynomialFunction G
  let i : B ⊗[k] B →ₐ[k] A ⊗[k] A := Algebra.TensorProduct.map B.val B.val
  have hi : Function.Injective i := by
    change Function.Injective
      (TensorProduct.map B.toSubmodule.subtype B.toSubmodule.subtype)
    exact TensorProduct.map_injective_of_flat_flat (R := k)
      B.toSubmodule.subtype B.toSubmodule.subtype
      B.toSubmodule.subtype_injective B.toSubmodule.subtype_injective
  let pre : B → B ⊗[k] B := fun f => Classical.choose
    (AlgebraicGroup.exists_rightInvariantTensor_comultiplication H hN f.val f.property)
  have hpre : ∀ f : B, i (pre f) = AlgebraicGroup.coordinateComultiplication G f.val := by
    intro f
    change TensorProduct.map B.toSubmodule.subtype B.toSubmodule.subtype (pre f) = _
    exact Classical.choose_spec
      (AlgebraicGroup.exists_rightInvariantTensor_comultiplication H hN f.val f.property)
  refine
    { toFun := pre
      map_one' := hi ?_
      map_mul' := fun x y => hi ?_
      map_zero' := hi ?_
      map_add' := fun x y => hi ?_
      commutes' := fun r => hi ?_ }
  · rw [hpre]
    simp [i]
  · rw [hpre (x * y), map_mul, hpre x, hpre y]
    exact map_mul _ _ _
  · rw [hpre]
    simp [i]
  · rw [hpre (x + y), map_add, hpre x, hpre y]
    exact map_add _ _ _
  · rw [hpre]
    simp [i]

end

/-! Ambient compatibility of the descended invariant comultiplication. -/

section
open scoped TensorProduct
variable {k : Type u} [Field k]

public lemma rightInvariantCoordinateComultiplication_apply
    {G : Variety k} [AlgebraicGroup G] (H : ClosedSubgroup G)
    (hN : H.toSubgroup.Normal)
    (f : AlgebraicGroup.rightInvariantCoordinateRing H) :
    TensorProduct.map
        (AlgebraicGroup.rightInvariantCoordinateRing H).toSubmodule.subtype
        (AlgebraicGroup.rightInvariantCoordinateRing H).toSubmodule.subtype
        (AlgebraicGroup.rightInvariantCoordinateComultiplication H hN f) =
      AlgebraicGroup.coordinateComultiplication G f.val := by
  rw [AlgebraicGroup.rightInvariantCoordinateComultiplication]
  exact Classical.choose_spec
    (AlgebraicGroup.exists_rightInvariantTensor_comultiplication
      H hN f.val f.property)

end

/-! Evaluation formula for the invariant coordinate counit. -/

section
variable {k : Type u} [Field k]

public lemma rightInvariantCoordinateCounit_apply
    {G : Variety k} [AlgebraicGroup G] (H : ClosedSubgroup G)
    (f : AlgebraicGroup.rightInvariantCoordinateRing H) :
    AlgebraicGroup.rightInvariantCoordinateCounit H f = f.val 1 := by
  exact AlgebraicGroup.coordinateCounit_apply G f.val

end

/-! Tensor-power inclusions of a right-invariant coordinate subalgebra. -/

section

open scoped TensorProduct

variable {k : Type u} [Field k]

/-- Inclusion of the invariant tensor square into the ambient tensor square. -/
@[expose]
public noncomputable def rightInvariantCoordinateTensorInclusion
    {G : Variety k} [AlgebraicGroup G] (H : ClosedSubgroup G) :
    AlgebraicGroup.rightInvariantCoordinateRing H ⊗[k]
        AlgebraicGroup.rightInvariantCoordinateRing H →ₐ[k]
      Variety.PolynomialFunction G ⊗[k] Variety.PolynomialFunction G :=
  Algebra.TensorProduct.map
    (AlgebraicGroup.rightInvariantCoordinateRing H).val
    (AlgebraicGroup.rightInvariantCoordinateRing H).val

public lemma rightInvariantCoordinateTensorInclusion_injective
    {G : Variety k} [AlgebraicGroup G] (H : ClosedSubgroup G) :
    Function.Injective
      (AlgebraicGroup.rightInvariantCoordinateTensorInclusion H) := by
  change Function.Injective
    (TensorProduct.map
      (AlgebraicGroup.rightInvariantCoordinateRing H).toSubmodule.subtype
      (AlgebraicGroup.rightInvariantCoordinateRing H).toSubmodule.subtype)
  exact TensorProduct.map_injective_of_flat_flat (R := k)
    _ _
    (AlgebraicGroup.rightInvariantCoordinateRing H).toSubmodule.subtype_injective
    (AlgebraicGroup.rightInvariantCoordinateRing H).toSubmodule.subtype_injective

/-- Inclusion of the right-associated invariant tensor cube. -/
@[expose]
public noncomputable def rightInvariantCoordinateRightTripleInclusion
    {G : Variety k} [AlgebraicGroup G] (H : ClosedSubgroup G) :
    AlgebraicGroup.rightInvariantCoordinateRing H ⊗[k]
        (AlgebraicGroup.rightInvariantCoordinateRing H ⊗[k]
          AlgebraicGroup.rightInvariantCoordinateRing H) →ₐ[k]
      Variety.PolynomialFunction G ⊗[k]
        (Variety.PolynomialFunction G ⊗[k] Variety.PolynomialFunction G) :=
  Algebra.TensorProduct.map
    (AlgebraicGroup.rightInvariantCoordinateRing H).val
    (AlgebraicGroup.rightInvariantCoordinateTensorInclusion H)

public lemma rightInvariantCoordinateRightTripleInclusion_injective
    {G : Variety k} [AlgebraicGroup G] (H : ClosedSubgroup G) :
    Function.Injective
      (AlgebraicGroup.rightInvariantCoordinateRightTripleInclusion H) := by
  change Function.Injective
    (TensorProduct.map
      (AlgebraicGroup.rightInvariantCoordinateRing H).toSubmodule.subtype
      (AlgebraicGroup.rightInvariantCoordinateTensorInclusion H).toLinearMap)
  exact TensorProduct.map_injective_of_flat_flat (R := k)
    _ _
    (AlgebraicGroup.rightInvariantCoordinateRing H).toSubmodule.subtype_injective
    (AlgebraicGroup.rightInvariantCoordinateTensorInclusion_injective H)

end

/-! The left counit identity on normal right-invariant coordinates. -/

section
open scoped TensorProduct
variable {k : Type u} [Field k]

public lemma rightInvariantCoordinateComultiplication_counit_left
    {G : Variety k} [AlgebraicGroup G] (H : ClosedSubgroup G)
    (hN : H.toSubgroup.Normal) :
    (Algebra.TensorProduct.map
      (AlgebraicGroup.rightInvariantCoordinateCounit H)
      (.id k (AlgebraicGroup.rightInvariantCoordinateRing H))).comp
        (AlgebraicGroup.rightInvariantCoordinateComultiplication H hN) =
      (Algebra.TensorProduct.lid k
        (AlgebraicGroup.rightInvariantCoordinateRing H)).symm := by
  let B := AlgebraicGroup.rightInvariantCoordinateRing H
  apply AlgHom.ext
  intro f
  apply (Algebra.TensorProduct.lid k B).injective
  apply Subtype.ext
  apply Variety.PolynomialFunction.ext
  intro x
  rw [AlgHom.comp_apply]
  let t := AlgebraicGroup.rightInvariantCoordinateComultiplication H hN f
  have ht :
      ((Algebra.TensorProduct.lid k B)
        (Algebra.TensorProduct.map
          (AlgebraicGroup.rightInvariantCoordinateCounit H)
          (.id k B) t)).val x =
        polynomialFunctionTensor G G
          (AlgebraicGroup.rightInvariantCoordinateTensorInclusion H t)
          ((Variety.prodPointEquiv G G).symm (1, x)) := by
    induction t using TensorProduct.induction_on with
    | zero => simp
    | add a b ha hb =>
        rw [map_add, map_add, map_add, map_add]
        simpa [Variety.PolynomialFunction.toFun] using congrArg₂ (· + ·) ha hb
    | tmul a b =>
        rw [Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.lid_tmul]
        change _ = polynomialFunctionTensor G G
          (Algebra.TensorProduct.map B.val B.val (a ⊗ₜ[k] b)) _
        rw [Algebra.TensorProduct.map_tmul, polynomialFunctionTensor_tmul,
          AlgebraicGroup.rightInvariantCoordinateCounit_apply]
        simp [polynomialFunction_mul_apply, polynomialFunctionLeft_apply,
          polynomialFunctionRight_apply, polynomialFunction_smul_apply]
  calc
    ((Algebra.TensorProduct.lid k B)
        (Algebra.TensorProduct.map
          (AlgebraicGroup.rightInvariantCoordinateCounit H)
          (.id k B) t)).val x =
      polynomialFunctionTensor G G
        (AlgebraicGroup.rightInvariantCoordinateTensorInclusion H t)
        ((Variety.prodPointEquiv G G).symm (1, x)) := ht
    _ = polynomialFunctionTensor G G
        (AlgebraicGroup.coordinateComultiplication G f.val)
        ((Variety.prodPointEquiv G G).symm (1, x)) := by
      have hcompat :=
        AlgebraicGroup.rightInvariantCoordinateComultiplication_apply H hN f
      change AlgebraicGroup.rightInvariantCoordinateTensorInclusion H t =
        AlgebraicGroup.coordinateComultiplication G f.val at hcompat
      rw [hcompat]
    _ = f.val (1 * x) := AlgebraicGroup.coordinateComultiplication_apply G f.val 1 x
    _ = f.val x := by rw [one_mul]
    _ = ((Algebra.TensorProduct.lid k B)
        ((Algebra.TensorProduct.lid k B).symm f)).val x := by
      exact congrArg (fun g : B => g.val x)
        ((Algebra.TensorProduct.lid k B).apply_symm_apply f).symm

end

/-! The right counit identity on normal right-invariant coordinates. -/

section
open scoped TensorProduct
variable {k : Type u} [Field k]

public lemma rightInvariantCoordinateComultiplication_counit_right
    {G : Variety k} [AlgebraicGroup G] (H : ClosedSubgroup G)
    (hN : H.toSubgroup.Normal) :
    (Algebra.TensorProduct.map
      (.id k (AlgebraicGroup.rightInvariantCoordinateRing H))
      (AlgebraicGroup.rightInvariantCoordinateCounit H)).comp
        (AlgebraicGroup.rightInvariantCoordinateComultiplication H hN) =
      (Algebra.TensorProduct.rid k k
        (AlgebraicGroup.rightInvariantCoordinateRing H)).symm := by
  let B := AlgebraicGroup.rightInvariantCoordinateRing H
  apply AlgHom.ext
  intro f
  apply (Algebra.TensorProduct.rid k k B).injective
  apply Subtype.ext
  apply Variety.PolynomialFunction.ext
  intro x
  rw [AlgHom.comp_apply]
  let t := AlgebraicGroup.rightInvariantCoordinateComultiplication H hN f
  have ht :
      ((Algebra.TensorProduct.rid k k B)
        (Algebra.TensorProduct.map
          (.id k B)
          (AlgebraicGroup.rightInvariantCoordinateCounit H) t)).val x =
        polynomialFunctionTensor G G
          (AlgebraicGroup.rightInvariantCoordinateTensorInclusion H t)
          ((Variety.prodPointEquiv G G).symm (x, 1)) := by
    induction t using TensorProduct.induction_on with
    | zero => simp
    | add a b ha hb =>
        rw [map_add, map_add, map_add, map_add]
        simpa [Variety.PolynomialFunction.toFun] using congrArg₂ (· + ·) ha hb
    | tmul a b =>
        rw [Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.rid_tmul]
        change _ = polynomialFunctionTensor G G
          (Algebra.TensorProduct.map B.val B.val (a ⊗ₜ[k] b)) _
        rw [Algebra.TensorProduct.map_tmul, polynomialFunctionTensor_tmul,
          AlgebraicGroup.rightInvariantCoordinateCounit_apply]
        simp only [polynomialFunction_mul_apply, polynomialFunctionLeft_apply,
          polynomialFunctionRight_apply, Equiv.apply_symm_apply, AlgHom.id_apply]
        rw [show ((b.val 1 • a : B).val) = b.val 1 • a.val by rfl,
          polynomialFunction_smul_apply]
        exact mul_comm _ _
  calc
    ((Algebra.TensorProduct.rid k k B)
        (Algebra.TensorProduct.map
          (.id k B)
          (AlgebraicGroup.rightInvariantCoordinateCounit H) t)).val x =
      polynomialFunctionTensor G G
        (AlgebraicGroup.rightInvariantCoordinateTensorInclusion H t)
        ((Variety.prodPointEquiv G G).symm (x, 1)) := ht
    _ = polynomialFunctionTensor G G
        (AlgebraicGroup.coordinateComultiplication G f.val)
        ((Variety.prodPointEquiv G G).symm (x, 1)) := by
      have hcompat :=
        AlgebraicGroup.rightInvariantCoordinateComultiplication_apply H hN f
      change AlgebraicGroup.rightInvariantCoordinateTensorInclusion H t =
        AlgebraicGroup.coordinateComultiplication G f.val at hcompat
      rw [hcompat]
    _ = f.val (x * 1) := AlgebraicGroup.coordinateComultiplication_apply G f.val x 1
    _ = f.val x := by rw [mul_one]
    _ = ((Algebra.TensorProduct.rid k k B)
        ((Algebra.TensorProduct.rid k k B).symm f)).val x := by
      exact congrArg (fun g : B => g.val x)
        ((Algebra.TensorProduct.rid k k B).apply_symm_apply f).symm

end

/-! Naturality of the descended comultiplication under coordinate inclusion. -/

section

variable {k : Type u} [Field k]

public lemma rightInvariantCoordinateComultiplication_natural
    {G : Variety k} [AlgebraicGroup G] (H : ClosedSubgroup G)
    (hN : H.toSubgroup.Normal) :
    (AlgebraicGroup.rightInvariantCoordinateTensorInclusion H).comp
        (AlgebraicGroup.rightInvariantCoordinateComultiplication H hN) =
      (AlgebraicGroup.coordinateComultiplication G).comp
        (AlgebraicGroup.rightInvariantCoordinateRing H).val := by
  apply AlgHom.ext
  intro f
  exact AlgebraicGroup.rightInvariantCoordinateComultiplication_apply H hN f

end

/-! Coassociativity of the descended normal right-invariant comultiplication. -/

section
open scoped TensorProduct
variable {k : Type u} [Field k]

public lemma rightInvariantCoordinateComultiplication_coassoc
    {G : Variety k} [AlgebraicGroup G] (H : ClosedSubgroup G)
    (hN : H.toSubgroup.Normal) :
    (Algebra.TensorProduct.assoc k k k
      (AlgebraicGroup.rightInvariantCoordinateRing H)
      (AlgebraicGroup.rightInvariantCoordinateRing H)
      (AlgebraicGroup.rightInvariantCoordinateRing H)).toAlgHom.comp
      ((Algebra.TensorProduct.map
        (AlgebraicGroup.rightInvariantCoordinateComultiplication H hN)
        (.id k (AlgebraicGroup.rightInvariantCoordinateRing H))).comp
        (AlgebraicGroup.rightInvariantCoordinateComultiplication H hN)) =
    (Algebra.TensorProduct.map
      (.id k (AlgebraicGroup.rightInvariantCoordinateRing H))
      (AlgebraicGroup.rightInvariantCoordinateComultiplication H hN)).comp
        (AlgebraicGroup.rightInvariantCoordinateComultiplication H hN) := by
  let B := AlgebraicGroup.rightInvariantCoordinateRing H
  let A := Variety.PolynomialFunction G
  let i : B →ₐ[k] A := B.val
  let i2 : B ⊗[k] B →ₐ[k] A ⊗[k] A :=
    AlgebraicGroup.rightInvariantCoordinateTensorInclusion H
  let i3 : B ⊗[k] (B ⊗[k] B) →ₐ[k] A ⊗[k] (A ⊗[k] A) :=
    AlgebraicGroup.rightInvariantCoordinateRightTripleInclusion H
  let dB : B →ₐ[k] B ⊗[k] B :=
    AlgebraicGroup.rightInvariantCoordinateComultiplication H hN
  let dA : A →ₐ[k] A ⊗[k] A := AlgebraicGroup.coordinateComultiplication G
  have hn : i2.comp dB = dA.comp i := by
    exact AlgebraicGroup.rightInvariantCoordinateComultiplication_natural H hN
  apply AlgHom.ext
  intro f
  apply AlgebraicGroup.rightInvariantCoordinateRightTripleInclusion_injective H
  change i3
      ((Algebra.TensorProduct.assoc k k k B B B)
        (Algebra.TensorProduct.map dB (.id k B) (dB f))) =
    i3 (Algebra.TensorProduct.map (.id k B) dB (dB f))
  change TensorProduct.map i.toLinearMap
      (TensorProduct.map i.toLinearMap i.toLinearMap)
      ((TensorProduct.assoc k B B B)
        (TensorProduct.map dB.toLinearMap (LinearMap.id) (dB f))) =
    TensorProduct.map i.toLinearMap
      (TensorProduct.map i.toLinearMap i.toLinearMap)
      (TensorProduct.map LinearMap.id dB.toLinearMap (dB f))
  rw [TensorProduct.map_map_assoc]
  have hnlin : i2.toLinearMap ∘ₗ dB.toLinearMap = dA.toLinearMap ∘ₗ i.toLinearMap := by
    exact congrArg AlgHom.toLinearMap hn
  have hf : i2 (dB f) = dA (i f) := by
    have := congrArg (fun F : B →ₐ[k] A ⊗[k] A => F f) hn
    simpa only [AlgHom.comp_apply] using this
  calc
    (TensorProduct.assoc k A A A)
        (TensorProduct.map i2.toLinearMap i.toLinearMap
          (TensorProduct.map dB.toLinearMap LinearMap.id (dB f))) =
      (TensorProduct.assoc k A A A)
        (TensorProduct.map (i2.toLinearMap ∘ₗ dB.toLinearMap)
          (i.toLinearMap ∘ₗ LinearMap.id) (dB f)) := by
            rw [TensorProduct.map_map]
    _ = (TensorProduct.assoc k A A A)
        (TensorProduct.map (dA.toLinearMap ∘ₗ i.toLinearMap)
          i.toLinearMap (dB f)) := by rw [hnlin]; rfl
    _ = (TensorProduct.assoc k A A A)
        (TensorProduct.map dA.toLinearMap LinearMap.id
          (TensorProduct.map i.toLinearMap i.toLinearMap (dB f))) := by
          rw [TensorProduct.map_map]
          rfl
    _ = (TensorProduct.assoc k A A A)
        (TensorProduct.map dA.toLinearMap LinearMap.id (i2 (dB f))) := rfl
    _ = (TensorProduct.assoc k A A A)
        (TensorProduct.map dA.toLinearMap LinearMap.id (dA (i f))) := by rw [hf]
    _ = TensorProduct.map LinearMap.id dA.toLinearMap (dA (i f)) := by
      have hcolin := congrArg AlgHom.toLinearMap
        (AlgebraicGroup.coordinateComultiplication_coassoc G)
      exact LinearMap.congr_fun hcolin (i f)
    _ = TensorProduct.map LinearMap.id dA.toLinearMap (i2 (dB f)) := by rw [hf]
    _ = TensorProduct.map LinearMap.id dA.toLinearMap
        (TensorProduct.map i.toLinearMap i.toLinearMap (dB f)) := rfl
    _ = TensorProduct.map i.toLinearMap
        (dA.toLinearMap ∘ₗ i.toLinearMap) (dB f) := by
      rw [TensorProduct.map_map]
      rfl
    _ = TensorProduct.map i.toLinearMap
        (i2.toLinearMap ∘ₗ dB.toLinearMap) (dB f) := by rw [hnlin]
    _ = TensorProduct.map i.toLinearMap i2.toLinearMap
        (TensorProduct.map LinearMap.id dB.toLinearMap (dB f)) := by
      rw [TensorProduct.map_map]
      rfl

end

/-! Normal right-invariant coordinates as a bialgebra. -/

section

variable {k : Type u} [Field k]

/-- The bialgebra structure descended to the normal right-invariant coordinate
subalgebra. -/
@[expose, implicit_reducible]
public noncomputable def rightInvariantCoordinateBialgebra
    {G : Variety k} [AlgebraicGroup G] (H : ClosedSubgroup G)
    (hN : H.toSubgroup.Normal) :
    Bialgebra k (AlgebraicGroup.rightInvariantCoordinateRing H) :=
  Bialgebra.ofAlgHom
    (AlgebraicGroup.rightInvariantCoordinateComultiplication H hN)
    (AlgebraicGroup.rightInvariantCoordinateCounit H)
    (AlgebraicGroup.rightInvariantCoordinateComultiplication_coassoc H hN)
    (AlgebraicGroup.rightInvariantCoordinateComultiplication_counit_left H hN)
    (AlgebraicGroup.rightInvariantCoordinateComultiplication_counit_right H hN)

end

/-! The left antipode identity on normal right-invariant coordinates. -/

section
open scoped TensorProduct
variable {k : Type u} [Field k]

public lemma rightInvariantCoordinateAntipode_mul_left
    {G : Variety k} [AlgebraicGroup G] (H : ClosedSubgroup G)
    (hN : H.toSubgroup.Normal) :
    ((Algebra.TensorProduct.lift
      (AlgebraicGroup.rightInvariantCoordinateAntipode H hN)
      (.id k (AlgebraicGroup.rightInvariantCoordinateRing H))
      (fun _ _ => Commute.all _ _)).comp
        (AlgebraicGroup.rightInvariantCoordinateComultiplication H hN)) =
      (Algebra.ofId k (AlgebraicGroup.rightInvariantCoordinateRing H)).comp
        (AlgebraicGroup.rightInvariantCoordinateCounit H) := by
  let B := AlgebraicGroup.rightInvariantCoordinateRing H
  apply AlgHom.ext
  intro f
  apply Subtype.ext
  apply Variety.PolynomialFunction.ext
  intro x
  rw [AlgHom.comp_apply, AlgHom.comp_apply]
  let t := AlgebraicGroup.rightInvariantCoordinateComultiplication H hN f
  have ht :
      (Algebra.TensorProduct.lift
          (AlgebraicGroup.rightInvariantCoordinateAntipode H hN)
          (.id k B) (fun _ _ => Commute.all _ _) t).val x =
        polynomialFunctionTensor G G
          (AlgebraicGroup.rightInvariantCoordinateTensorInclusion H t)
          ((Variety.prodPointEquiv G G).symm (x⁻¹, x)) := by
    induction t using TensorProduct.induction_on with
    | zero => simp
    | add a b ha hb =>
        rw [map_add, map_add, map_add]
        simpa [Variety.PolynomialFunction.toFun] using congrArg₂ (· + ·) ha hb
    | tmul a b =>
        rw [Algebra.TensorProduct.lift_tmul]
        change ((AlgebraicGroup.rightInvariantCoordinateAntipode H hN a) * b).val x =
          polynomialFunctionTensor G G
            (Algebra.TensorProduct.map B.val B.val (a ⊗ₜ[k] b)) _
        rw [Algebra.TensorProduct.map_tmul, polynomialFunctionTensor_tmul]
        have ha := AlgebraicGroup.rightInvariantCoordinateAntipode_apply H hN a
        change (AlgebraicGroup.rightInvariantCoordinateAntipode H hN a).val = _ at ha
        change ((AlgebraicGroup.rightInvariantCoordinateAntipode H hN a).val * b.val) x = _
        rw [ha]
        simp [polynomialFunction_mul_apply, polynomialFunctionLeft_apply,
          polynomialFunctionRight_apply, AlgebraicGroup.coordinateAntipode_apply]
  have hcompat :=
    AlgebraicGroup.rightInvariantCoordinateComultiplication_apply H hN f
  change AlgebraicGroup.rightInvariantCoordinateTensorInclusion H t =
    AlgebraicGroup.coordinateComultiplication G f.val at hcompat
  calc
    (Algebra.TensorProduct.lift
        (AlgebraicGroup.rightInvariantCoordinateAntipode H hN)
        (.id k B) (fun _ _ => Commute.all _ _) t).val x =
      polynomialFunctionTensor G G
        (AlgebraicGroup.rightInvariantCoordinateTensorInclusion H t)
        ((Variety.prodPointEquiv G G).symm (x⁻¹, x)) := ht
    _ = polynomialFunctionTensor G G
        (AlgebraicGroup.coordinateComultiplication G f.val)
        ((Variety.prodPointEquiv G G).symm (x⁻¹, x)) := by rw [hcompat]
    _ = f.val (x⁻¹ * x) := AlgebraicGroup.coordinateComultiplication_apply G f.val x⁻¹ x
    _ = f.val 1 := by rw [inv_mul_cancel]
    _ = (algebraMap k B (AlgebraicGroup.rightInvariantCoordinateCounit H f)).val x := by
      rw [AlgebraicGroup.rightInvariantCoordinateCounit_apply]
      exact polynomialFunction_algebraMap_apply G (f.val 1) x |>.symm

end

/-! The right antipode identity on normal right-invariant coordinates. -/

section
open scoped TensorProduct
variable {k : Type u} [Field k]

public lemma rightInvariantCoordinateAntipode_mul_right
    {G : Variety k} [AlgebraicGroup G] (H : ClosedSubgroup G)
    (hN : H.toSubgroup.Normal) :
    ((Algebra.TensorProduct.lift
      (.id k (AlgebraicGroup.rightInvariantCoordinateRing H))
      (AlgebraicGroup.rightInvariantCoordinateAntipode H hN)
      (fun _ _ => Commute.all _ _)).comp
        (AlgebraicGroup.rightInvariantCoordinateComultiplication H hN)) =
      (Algebra.ofId k (AlgebraicGroup.rightInvariantCoordinateRing H)).comp
        (AlgebraicGroup.rightInvariantCoordinateCounit H) := by
  let B := AlgebraicGroup.rightInvariantCoordinateRing H
  apply AlgHom.ext
  intro f
  apply Subtype.ext
  apply Variety.PolynomialFunction.ext
  intro x
  rw [AlgHom.comp_apply, AlgHom.comp_apply]
  let t := AlgebraicGroup.rightInvariantCoordinateComultiplication H hN f
  have ht :
      (Algebra.TensorProduct.lift
          (.id k B)
          (AlgebraicGroup.rightInvariantCoordinateAntipode H hN) (fun _ _ => Commute.all _ _) t).val x =
        polynomialFunctionTensor G G
          (AlgebraicGroup.rightInvariantCoordinateTensorInclusion H t)
          ((Variety.prodPointEquiv G G).symm (x, x⁻¹)) := by
    induction t using TensorProduct.induction_on with
    | zero => simp
    | add a b ha hb =>
        rw [map_add, map_add, map_add]
        simpa [Variety.PolynomialFunction.toFun] using congrArg₂ (· + ·) ha hb
    | tmul a b =>
        rw [Algebra.TensorProduct.lift_tmul]
        change (a * (AlgebraicGroup.rightInvariantCoordinateAntipode H hN b)).val x =
          polynomialFunctionTensor G G
            (Algebra.TensorProduct.map B.val B.val (a ⊗ₜ[k] b)) _
        rw [Algebra.TensorProduct.map_tmul, polynomialFunctionTensor_tmul]
        have hb := AlgebraicGroup.rightInvariantCoordinateAntipode_apply H hN b
        change (AlgebraicGroup.rightInvariantCoordinateAntipode H hN b).val = _ at hb
        change (a.val * (AlgebraicGroup.rightInvariantCoordinateAntipode H hN b).val) x = _
        rw [hb]
        simp [polynomialFunction_mul_apply, polynomialFunctionLeft_apply,
          polynomialFunctionRight_apply, AlgebraicGroup.coordinateAntipode_apply]
  have hcompat :=
    AlgebraicGroup.rightInvariantCoordinateComultiplication_apply H hN f
  change AlgebraicGroup.rightInvariantCoordinateTensorInclusion H t =
    AlgebraicGroup.coordinateComultiplication G f.val at hcompat
  calc
    (Algebra.TensorProduct.lift
        (.id k B)
        (AlgebraicGroup.rightInvariantCoordinateAntipode H hN) (fun _ _ => Commute.all _ _) t).val x =
      polynomialFunctionTensor G G
        (AlgebraicGroup.rightInvariantCoordinateTensorInclusion H t)
        ((Variety.prodPointEquiv G G).symm (x, x⁻¹)) := ht
    _ = polynomialFunctionTensor G G
        (AlgebraicGroup.coordinateComultiplication G f.val)
        ((Variety.prodPointEquiv G G).symm (x, x⁻¹)) := by rw [hcompat]
    _ = f.val (x * x⁻¹) := AlgebraicGroup.coordinateComultiplication_apply G f.val x x⁻¹
    _ = f.val 1 := by rw [mul_inv_cancel]
    _ = (algebraMap k B (AlgebraicGroup.rightInvariantCoordinateCounit H f)).val x := by
      rw [AlgebraicGroup.rightInvariantCoordinateCounit_apply]
      exact polynomialFunction_algebraMap_apply G (f.val 1) x |>.symm

end

/-! Normal right-invariant coordinates as a Hopf algebra. -/

section

variable {k : Type u} [Field k]

/-- The Hopf algebra structure descended to the normal right-invariant
coordinate subalgebra. -/
@[expose, implicit_reducible]
public noncomputable def rightInvariantCoordinateHopfAlgebra
    {G : Variety k} [AlgebraicGroup G] (H : ClosedSubgroup G)
    (hN : H.toSubgroup.Normal) :
    HopfAlgebra k (AlgebraicGroup.rightInvariantCoordinateRing H) := by
  letI : Bialgebra k (AlgebraicGroup.rightInvariantCoordinateRing H) :=
    AlgebraicGroup.rightInvariantCoordinateBialgebra H hN
  exact HopfAlgebra.ofAlgHom
    (AlgebraicGroup.rightInvariantCoordinateAntipode H hN)
    (AlgebraicGroup.rightInvariantCoordinateAntipode_mul_left H hN)
    (AlgebraicGroup.rightInvariantCoordinateAntipode_mul_right H hN)

end

/-! The right-invariant coordinate subalgebra is reduced. -/

section

variable {k : Type u} [Field k]

public instance rightInvariantCoordinateRing_isReduced
    {G : Variety k} [AlgebraicGroup G] (H : ClosedSubgroup G) :
    IsReduced (AlgebraicGroup.rightInvariantCoordinateRing H) :=
  isReduced_of_injective (Subalgebra.val _) Subtype.val_injective

end
end Theory.AlgebraicGroup

