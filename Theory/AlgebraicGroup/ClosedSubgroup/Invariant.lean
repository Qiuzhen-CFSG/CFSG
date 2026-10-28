module

public import Theory.AlgebraicGroup.ClosedSubgroup.Action
public import Theory.AlgebraicGroup.CoordinateRing.Basic

universe u

/-!
Polynomial functions invariant under right translation by a closed subgroup.
This is the candidate coordinate algebra for the homogeneous-space quotient.
-/

namespace Theory.AlgebraicGroup

section

variable {k : Type u} [Field k]

/-- The `k`-subalgebra of polynomial functions on `G` fixed by every right
translation by a point of `H`. -/
@[expose]
public def rightInvariantCoordinateRing
    {G : Variety k} [AlgebraicGroup G] (H : ClosedSubgroup G) :
    Subalgebra k (Variety.PolynomialFunction G) where
  carrier := {f | ∀ h : Variety.Point G, h ∈ H.toSubgroup →
    (AlgebraicGroup.rightMulMorphism G h).pullbackAlgHom f = f}
  zero_mem' := by
    intro h hh
    exact map_zero _
  one_mem' := by
    intro h hh
    exact map_one _
  add_mem' := by
    intro f g hf hg h hh
    rw [map_add, hf h hh, hg h hh]
  mul_mem' := by
    intro f g hf hg h hh
    rw [map_mul, hf h hh, hg h hh]
  algebraMap_mem' := by
    intro r h hh
    exact (AlgebraicGroup.rightMulMorphism G h).pullbackAlgHom.commutes r

/-! Evaluation at the identity, restricted to right-invariant coordinates. -/

@[expose]
public noncomputable def rightInvariantCoordinateCounit
    {G : Variety k} [AlgebraicGroup G] (H : ClosedSubgroup G) :
    rightInvariantCoordinateRing H →ₐ[k] k :=
  (AlgebraicGroup.coordinateCounit G).comp
    (rightInvariantCoordinateRing H).val

/-- Membership in the right-invariant coordinate algebra is the expected
pointwise invariance identity. -/
public lemma mem_rightInvariantCoordinateRing_iff
    {G : Variety k} [AlgebraicGroup G] (H : ClosedSubgroup G)
    (f : Variety.PolynomialFunction G) :
    f ∈ AlgebraicGroup.rightInvariantCoordinateRing H ↔
      ∀ (g h : Variety.Point G), h ∈ H.toSubgroup → f (g * h) = f g := by
  constructor
  · intro hf g h hh
    have hfixed := hf h hh
    have hvalue := congrArg (fun a : Variety.PolynomialFunction G ↦ a g) hfixed
    change f ((AlgebraicGroup.rightMulMorphism G h).toFun g) = f g at hvalue
    rw [AlgebraicGroup.rightMulMorphism_apply] at hvalue
    exact hvalue
  · intro hf h hh
    apply Variety.PolynomialFunction.ext
    intro g
    change f ((AlgebraicGroup.rightMulMorphism G h).toFun g) = f g
    rw [AlgebraicGroup.rightMulMorphism_apply]
    exact hf g h hh

end

variable {k : Type u} [Field k]

/-! Normal right-invariants are stable under the coordinate antipode. -/

public lemma coordinateAntipode_mem_rightInvariantCoordinateRing
    {G : Variety k} [AlgebraicGroup G] (H : ClosedSubgroup G)
    (hN : H.toSubgroup.Normal) (f : Variety.PolynomialFunction G)
    (hf : f ∈ rightInvariantCoordinateRing H) :
    coordinateAntipode G f ∈ rightInvariantCoordinateRing H := by
  rw [mem_rightInvariantCoordinateRing_iff] at hf ⊢
  intro g h hh
  rw [coordinateAntipode_apply, coordinateAntipode_apply]
  have hconj : g * h⁻¹ * g⁻¹ ∈ H.toSubgroup :=
    hN.conj_mem h⁻¹ (H.toSubgroup.inv_mem hh) g
  calc
    f (g * h)⁻¹ = f (h⁻¹ * g⁻¹) := by rw [mul_inv_rev]
    _ = f (g⁻¹ * (g * h⁻¹ * g⁻¹)) := by simp [mul_assoc]
    _ = f g⁻¹ := hf g⁻¹ (g * h⁻¹ * g⁻¹) hconj

/-! Right-invariant coordinates are exactly the coinvariants of the subgroup coaction. -/

section
open scoped TensorProduct
variable {k : Type u} [Field k]

public lemma mem_rightInvariantCoordinateRing_iff_coaction
    {G : Variety k} [AlgebraicGroup G] (H : ClosedSubgroup G)
    (f : Variety.PolynomialFunction G) :
    f ∈ AlgebraicGroup.rightInvariantCoordinateRing H ↔
      H.coordinateCoaction f =
        f ⊗ₜ[k] (1 : Variety.PolynomialFunction H.carrierVariety) := by
  rw [AlgebraicGroup.mem_rightInvariantCoordinateRing_iff]
  constructor
  · intro hf
    apply (polynomialFunction_prod_algEquiv G H.carrierVariety).injective
    apply Variety.PolynomialFunction.ext
    intro z
    let gh := Variety.prodPointEquiv G H.carrierVariety z
    let g := gh.1
    let h := gh.2
    have hz : z =
        (Variety.prodPointEquiv G H.carrierVariety).symm (g, h) := by
      exact ((Variety.prodPointEquiv G H.carrierVariety).symm_apply_apply z).symm
    change polynomialFunctionTensor G H.carrierVariety (H.coordinateCoaction f) z =
      polynomialFunctionTensor G H.carrierVariety (f ⊗ₜ[k] 1) z
    rw [hz, ClosedSubgroup.coordinateCoaction_apply,
      polynomialFunctionTensor_tmul]
    simp only [map_one, mul_one]
    apply hf g (H.inclusion.onPoints h)
    change H.inclusion.onPoints h ∈ (H.toSubgroup : Set (Variety.Point G))
    rw [← H.range_inclusion]
    exact ⟨h, rfl⟩
  · intro hco g h hh
    have hh' : h ∈ (H.toSubgroup : Set (Variety.Point G)) := hh
    rw [← H.range_inclusion] at hh'
    obtain ⟨h', rfl⟩ := hh'
    have heval := congrArg
      (fun t : Variety.PolynomialFunction G ⊗[k]
          Variety.PolynomialFunction H.carrierVariety =>
        polynomialFunctionTensor G H.carrierVariety t
          ((Variety.prodPointEquiv G H.carrierVariety).symm (g, h'))) hco
    rw [ClosedSubgroup.coordinateCoaction_apply,
      polynomialFunctionTensor_tmul] at heval
    simpa using heval

end

/-! The subgroup coordinate coaction as an algebra map over its coinvariants. -/

section
open scoped TensorProduct
variable {k : Type u} [Field k]

@[expose]
public noncomputable def ClosedSubgroup.coordinateCoactionOverInvariants
    {G : Variety k} [AlgebraicGroup G] (H : ClosedSubgroup G) :
    let B := AlgebraicGroup.rightInvariantCoordinateRing H
    let A := Variety.PolynomialFunction G
    let C := Variety.PolynomialFunction H.carrierVariety
    A →ₐ[B] A ⊗[k] C := by
  let B := AlgebraicGroup.rightInvariantCoordinateRing H
  let A := Variety.PolynomialFunction G
  let C := Variety.PolynomialFunction H.carrierVariety
  exact
    { H.coordinateCoaction with
      commutes' := by
        intro b
        change H.coordinateCoaction b.val = b.val ⊗ₜ[k] (1 : C)
        exact
          (AlgebraicGroup.mem_rightInvariantCoordinateRing_iff_coaction H b.val).mp
            b.property }

end

/-! The Hopf-Galois canonical map for a closed subgroup. -/

section
open scoped TensorProduct
variable {k : Type u} [Field k]

@[expose]
public noncomputable def ClosedSubgroup.canonicalMap
    {G : Variety k} [AlgebraicGroup G] (H : ClosedSubgroup G) :
    let B := AlgebraicGroup.rightInvariantCoordinateRing H
    let A := Variety.PolynomialFunction G
    let C := Variety.PolynomialFunction H.carrierVariety
    A ⊗[B] A →ₐ[B] A ⊗[k] C := by
  let B := AlgebraicGroup.rightInvariantCoordinateRing H
  let A := Variety.PolynomialFunction G
  let C := Variety.PolynomialFunction H.carrierVariety
  exact Algebra.TensorProduct.lift
    (Algebra.TensorProduct.includeLeft : A →ₐ[B] A ⊗[k] C)
    H.coordinateCoactionOverInvariants
    (fun _ _ => Commute.all _ _)

end

/-! Evaluation of the closed-subgroup canonical map on pure tensors. -/

section
open scoped TensorProduct
variable {k : Type u} [Field k]

@[simp]
public lemma ClosedSubgroup.canonicalMap_tmul
    {G : Variety k} [AlgebraicGroup G] (H : ClosedSubgroup G)
    (a b : Variety.PolynomialFunction G) :
    H.canonicalMap
        (a ⊗ₜ[AlgebraicGroup.rightInvariantCoordinateRing H] b) =
      (a ⊗ₜ[k] (1 : Variety.PolynomialFunction H.carrierVariety)) *
        H.coordinateCoaction b := by
  rfl

end

/-! Change of tensor base from the ground field to the invariant coordinate algebra. -/

section
open scoped TensorProduct
variable {k : Type u} [Field k]

@[expose]
public noncomputable def ClosedSubgroup.ambientTensorToInvariantTensor
    {G : Variety k} [AlgebraicGroup G] (H : ClosedSubgroup G) :
    let B := AlgebraicGroup.rightInvariantCoordinateRing H
    let A := Variety.PolynomialFunction G
    A ⊗[k] A →ₐ[k] A ⊗[B] A := by
  let B := AlgebraicGroup.rightInvariantCoordinateRing H
  let A := Variety.PolynomialFunction G
  exact Algebra.TensorProduct.lift
    ((Algebra.TensorProduct.includeLeft : A →ₐ[B] A ⊗[B] A).restrictScalars k)
    ((Algebra.TensorProduct.includeRight : A →ₐ[B] A ⊗[B] A).restrictScalars k)
    (fun _ _ => Commute.all _ _)

@[simp]
public lemma ClosedSubgroup.ambientTensorToInvariantTensor_tmul
    {G : Variety k} [AlgebraicGroup G] (H : ClosedSubgroup G)
    (a b : Variety.PolynomialFunction G) :
    H.ambientTensorToInvariantTensor (a ⊗ₜ[k] b) =
      a ⊗ₜ[AlgebraicGroup.rightInvariantCoordinateRing H] b := by
  simp [ClosedSubgroup.ambientTensorToInvariantTensor]

end

/-! Pointwise evaluation of the canonical map on an ambient tensor. -/

section
open scoped TensorProduct
variable {k : Type u} [Field k]

public lemma ClosedSubgroup.canonicalMap_ambientTensor_apply
    {G : Variety k} [AlgebraicGroup G] (H : ClosedSubgroup G)
    (t : Variety.PolynomialFunction G ⊗[k] Variety.PolynomialFunction G)
    (g : Variety.Point G) (h : Variety.Point H.carrierVariety) :
    polynomialFunctionTensor G H.carrierVariety
      (H.canonicalMap (H.ambientTensorToInvariantTensor t))
      ((Variety.prodPointEquiv G H.carrierVariety).symm (g, h)) =
    polynomialFunctionTensor G G t
      ((Variety.prodPointEquiv G G).symm
        (g, g * H.inclusion.onPoints h)) := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy =>
      simp only [map_add]
      simp only [Variety.PolynomialFunction.toFun, Subring.coe_add, Pi.add_apply]
      exact congrArg₂ (· + ·) hx hy
  | tmul a b =>
      rw [H.ambientTensorToInvariantTensor_tmul, H.canonicalMap_tmul,
        map_mul, polynomialFunctionTensor_tmul]
      change (a g * 1) *
          polynomialFunctionTensor G H.carrierVariety (H.coordinateCoaction b)
            ((Variety.prodPointEquiv G H.carrierVariety).symm (g, h)) =
        polynomialFunctionTensor G G (a ⊗ₜ[k] b)
          ((Variety.prodPointEquiv G G).symm
            (g, g * H.inclusion.onPoints h))
      rw [H.coordinateCoaction_apply, polynomialFunctionTensor_tmul]
      simp

end

/-! Restriction of ambient polynomial functions to a closed subgroup as an algebra map. -/

section
variable {k : Type u} [Field k]

@[expose]
public def ClosedSubgroup.restrictionAlgHom
    {G : Variety k} [AlgebraicGroup G] (H : ClosedSubgroup G) :
    Variety.PolynomialFunction G →ₐ[k]
      Variety.PolynomialFunction H.carrierVariety :=
  H.inclusion.toVariety.pullbackAlgHom

end

/-! Pointwise evaluation after applying the antipode to the left tensor factor. -/

section
open scoped TensorProduct
variable {k : Type u} [Field k]

public lemma coordinateAntipodeTensor_apply
    (G : Variety k) [AlgebraicGroup G]
    (t : Variety.PolynomialFunction G ⊗[k] Variety.PolynomialFunction G)
    (x y : Variety.Point G) :
    polynomialFunctionTensor G G
      (TensorProduct.map (AlgebraicGroup.coordinateAntipode G).toLinearMap
        LinearMap.id t)
      ((Variety.prodPointEquiv G G).symm (x, y)) =
    polynomialFunctionTensor G G t
      ((Variety.prodPointEquiv G G).symm (x⁻¹, y)) := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | add a b ha hb =>
      simp only [map_add]
      simp only [Variety.PolynomialFunction.toFun, Subring.coe_add, Pi.add_apply]
      exact congrArg₂ (· + ·) ha hb
  | tmul a b =>
      rw [TensorProduct.map_tmul, polynomialFunctionTensor_tmul,
        polynomialFunctionTensor_tmul]
      change (AlgebraicGroup.coordinateAntipode G a) x * b y = a x⁻¹ * b y
      rw [AlgebraicGroup.coordinateAntipode_apply]

end

/-! The translation tensor associated to an ambient coordinate function. -/

section
open scoped TensorProduct
variable {k : Type u} [Field k]

@[expose]
public noncomputable def ClosedSubgroup.translationTensor
    {G : Variety k} [AlgebraicGroup G] (H : ClosedSubgroup G)
    (b : Variety.PolynomialFunction G) :
    let B := AlgebraicGroup.rightInvariantCoordinateRing H
    Variety.PolynomialFunction G ⊗[B] Variety.PolynomialFunction G :=
  H.ambientTensorToInvariantTensor
    (TensorProduct.map (AlgebraicGroup.coordinateAntipode G).toLinearMap
      LinearMap.id (AlgebraicGroup.coordinateComultiplication G b))

end

/-! The canonical map sends a translation tensor to the restricted coordinate. -/

section
open scoped TensorProduct
variable {k : Type u} [Field k]

public lemma ClosedSubgroup.canonicalMap_translationTensor
    {G : Variety k} [AlgebraicGroup G] (H : ClosedSubgroup G)
    (b : Variety.PolynomialFunction G) :
    H.canonicalMap (H.translationTensor b) =
      (1 : Variety.PolynomialFunction G) ⊗ₜ[k] H.restrictionAlgHom b := by
  apply polynomialFunctionTensor_injective G H.carrierVariety
  apply Variety.PolynomialFunction.ext
  intro z
  let gh := Variety.prodPointEquiv G H.carrierVariety z
  let g := gh.1
  let h := gh.2
  have hz : z =
      (Variety.prodPointEquiv G H.carrierVariety).symm (g, h) := by
    exact ((Variety.prodPointEquiv G H.carrierVariety).symm_apply_apply z).symm
  rw [hz]
  change polynomialFunctionTensor G H.carrierVariety
      (H.canonicalMap (H.ambientTensorToInvariantTensor
        (TensorProduct.map (AlgebraicGroup.coordinateAntipode G).toLinearMap
          LinearMap.id (AlgebraicGroup.coordinateComultiplication G b)))) _ = _
  rw [H.canonicalMap_ambientTensor_apply,
    AlgebraicGroup.coordinateAntipodeTensor_apply,
    AlgebraicGroup.coordinateComultiplication_apply,
    polynomialFunctionTensor_tmul]
  change b (g⁻¹ * (g * H.inclusion.onPoints h)) =
    1 * b (H.inclusion.onPoints h)
  rw [← mul_assoc, inv_mul_cancel, one_mul, one_mul]

end

/-! Surjectivity of the Hopf-Galois canonical map for a closed subgroup. -/

section
open scoped TensorProduct
variable {k : Type u} [Field k]

public lemma ClosedSubgroup.canonicalMap_surjective
    {G : Variety k} [AlgebraicGroup G] (H : ClosedSubgroup G) :
    Function.Surjective H.canonicalMap := by
  intro t
  induction t using TensorProduct.induction_on with
  | zero => exact ⟨0, map_zero _⟩
  | add x y hx hy =>
      obtain ⟨x', rfl⟩ := hx
      obtain ⟨y', rfl⟩ := hy
      refine ⟨x' + y', ?_⟩
      rw [map_add]
  | tmul a c =>
      obtain ⟨b, hb⟩ := H.restrictionRingHom_surjective c
      refine ⟨(a ⊗ₜ[AlgebraicGroup.rightInvariantCoordinateRing H]
          (1 : Variety.PolynomialFunction G)) * H.translationTensor b, ?_⟩
      rw [map_mul, H.canonicalMap_tmul, H.canonicalMap_translationTensor]
      simp only [map_one, mul_one]
      rw [Algebra.TensorProduct.tmul_mul_tmul]
      change (a * 1) ⊗ₜ[k]
          ((1 : Variety.PolynomialFunction H.carrierVariety) *
            H.restrictionAlgHom b) = a ⊗ₜ[k] c
      simp only [mul_one, one_mul]
      congr 1

end

/-! The canonical map is compatible with multiplication by the left factor. -/

section
open scoped TensorProduct
variable {k : Type u} [Field k]

public lemma ClosedSubgroup.canonicalMap_leftMul
    {G : Variety k} [AlgebraicGroup G] (H : ClosedSubgroup G)
    (a : Variety.PolynomialFunction G)
    (x : (Variety.PolynomialFunction G) ⊗[AlgebraicGroup.rightInvariantCoordinateRing H]
      (Variety.PolynomialFunction G)) :
    H.canonicalMap ((Algebra.TensorProduct.includeLeft :
      Variety.PolynomialFunction G →ₐ[AlgebraicGroup.rightInvariantCoordinateRing H]
        (Variety.PolynomialFunction G) ⊗[AlgebraicGroup.rightInvariantCoordinateRing H]
          (Variety.PolynomialFunction G)) a * x) =
      (Algebra.TensorProduct.includeLeft :
        Variety.PolynomialFunction G →ₐ[k]
          (Variety.PolynomialFunction G) ⊗[k]
            Variety.PolynomialFunction H.carrierVariety) a * H.canonicalMap x := by
  rw [map_mul]
  congr 1
  change H.canonicalMap (a ⊗ₜ[AlgebraicGroup.rightInvariantCoordinateRing H]
      (1 : Variety.PolynomialFunction G)) =
    a ⊗ₜ[k] (1 : Variety.PolynomialFunction H.carrierVariety)
  rw [H.canonicalMap_tmul]
  simp

end
end Theory.AlgebraicGroup
