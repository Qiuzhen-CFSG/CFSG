module

public import Theory.AlgebraicGroup.CoordinateRing.Basic
import Mathlib.LinearAlgebra.Dual.Lemmas

universe u v w x

/-! Point evaluation restricted to a linear subspace of polynomial functions. -/

namespace Theory.AlgebraicGroup

section

variable {k : Type u} [Field k]

def polynomialFunctionSubmoduleEvaluation (G : Variety k)
    (W : Submodule k (Variety.PolynomialFunction G)) (x : Variety.Point G) :
    W →ₗ[k] k where
  toFun := fun f => f.val x
  map_add' := by
    intro f g
    rfl
  map_smul' := by
    intro c f
    change (c • f.val : Variety.PolynomialFunction G) x = c • f.val x
    rw [polynomialFunction_smul_apply]
    simp [smul_eq_mul]

end

/-! Point evaluations span the dual of a finite coordinate subspace. -/

section

variable {k : Type u} [Field k]

lemma Submodule.dual_mem_span_polynomialFunctionEvaluation
    (G : Variety k)
    (W : Submodule k (Variety.PolynomialFunction G)) (hW : W.FG)
    (K : Module.Dual k W) :
    K ∈ Submodule.span k
      (Set.range (polynomialFunctionSubmoduleEvaluation G W)) := by
  have : FiniteDimensional k W := (Submodule.fg_iff_finiteDimensional W).mp hW
  apply FiniteDimensional.mem_span_of_iInf_ker_le_ker
  intro f hf
  have hfzero : f = 0 := by
    apply Subtype.ext
    apply Variety.PolynomialFunction.ext
    intro x
    have hx : f ∈ LinearMap.ker
        (polynomialFunctionSubmoduleEvaluation G W x) :=
      (Submodule.mem_iInf _).1 hf x
    exact LinearMap.mem_ker.mp hx
  rw [hfzero]
  exact LinearMap.map_zero K

end

/-! Point slices of tensors of polynomial functions. -/

section
open scoped TensorProduct

variable {k : Type u} [Field k]

def polynomialFunctionEvaluationLinearMap (G : Variety k)
    (x : Variety.Point G) : Variety.PolynomialFunction G →ₗ[k] k where
  toFun := fun f => f x
  map_add' := by
    intro f g
    rfl
  map_smul' := by
    intro c f
    rw [polynomialFunction_smul_apply]
    simp [smul_eq_mul]

noncomputable def polynomialFunctionTensorLeftSlice (G : Variety k)
    (z : Variety.PolynomialFunction G ⊗[k] Variety.PolynomialFunction G)
    (x : Variety.Point G) : Variety.PolynomialFunction G :=
  TensorProduct.lid k _
    (((polynomialFunctionEvaluationLinearMap G x).rTensor _) z)

noncomputable def polynomialFunctionTensorRightSlice (G : Variety k)
    (z : Variety.PolynomialFunction G ⊗[k] Variety.PolynomialFunction G)
    (x : Variety.Point G) : Variety.PolynomialFunction G :=
  TensorProduct.rid k _
    (((polynomialFunctionEvaluationLinearMap G x).lTensor _) z)

end

/-! Evaluation formulas for left and right point slices of function tensors. -/

section
open scoped TensorProduct

variable {k : Type u} [Field k]

lemma polynomialFunctionTensorLeftSlice_apply (G : Variety k)
    (z : Variety.PolynomialFunction G ⊗[k] Variety.PolynomialFunction G)
    (x y : Variety.Point G) :
    polynomialFunctionTensorLeftSlice G z x y =
      polynomialFunctionTensor G G z
        ((Variety.prodPointEquiv G G).symm (x, y)) := by
  induction z with
  | zero => simp [polynomialFunctionTensorLeftSlice]
  | tmul f g =>
      rw [show polynomialFunctionTensorLeftSlice G (f ⊗ₜ[k] g) x =
          (f x) • g by
        unfold polynomialFunctionTensorLeftSlice
        rw [LinearMap.rTensor_tmul, TensorProduct.lid_tmul]
        rfl]
      rw [polynomialFunctionTensor_tmul]
      simp only [polynomialFunction_mul_apply, polynomialFunctionLeft_apply,
        polynomialFunctionRight_apply, Variety.prodPointEquiv,
        Equiv.apply_symm_apply, polynomialFunction_smul_apply]
  | add p q hp hq =>
      rw [show polynomialFunctionTensorLeftSlice G (p + q) x =
          polynomialFunctionTensorLeftSlice G p x +
            polynomialFunctionTensorLeftSlice G q x by
        simp [polynomialFunctionTensorLeftSlice],
        show polynomialFunctionTensor G G (p + q) =
          polynomialFunctionTensor G G p + polynomialFunctionTensor G G q by
        rw [map_add]]
      change polynomialFunctionTensorLeftSlice G p x y +
          polynomialFunctionTensorLeftSlice G q x y = _
      exact congrArg₂ (· + ·) hp hq
end

/-! Left point slices of coordinate comultiplication are left translates. -/

section

variable {k : Type u} [Field k]

lemma coordinateComultiplication_leftSlice
    (G : Variety k) [AlgebraicGroup G]
    (f : Variety.PolynomialFunction G) (x : Variety.Point G) :
    polynomialFunctionTensorLeftSlice G
        (AlgebraicGroup.coordinateComultiplication G f) x =
      (AlgebraicGroup.leftMulMorphism G x).pullbackAlgHom f := by
  apply Variety.PolynomialFunction.ext
  intro y
  rw [polynomialFunctionTensorLeftSlice_apply,
    AlgebraicGroup.coordinateComultiplication_apply]
  rfl

end

/-! Evaluation formula for right point slices of function tensors. -/

section
open scoped TensorProduct

variable {k : Type u} [Field k]

lemma polynomialFunctionTensorRightSlice_apply (G : Variety k)
    (z : Variety.PolynomialFunction G ⊗[k] Variety.PolynomialFunction G)
    (x y : Variety.Point G) :
    polynomialFunctionTensorRightSlice G z y x =
      polynomialFunctionTensor G G z
        ((Variety.prodPointEquiv G G).symm (x, y)) := by
  induction z with
  | zero => simp [polynomialFunctionTensorRightSlice]
  | tmul f g =>
      rw [show polynomialFunctionTensorRightSlice G (f ⊗ₜ[k] g) y =
          (g y) • f by
        unfold polynomialFunctionTensorRightSlice
        rw [LinearMap.lTensor_tmul, TensorProduct.rid_tmul]
        rfl]
      rw [polynomialFunctionTensor_tmul]
      simp only [polynomialFunction_mul_apply, polynomialFunctionLeft_apply,
        polynomialFunctionRight_apply, Variety.prodPointEquiv,
        Equiv.apply_symm_apply, polynomialFunction_smul_apply,
        mul_comm]
  | add p q hp hq =>
      rw [show polynomialFunctionTensorRightSlice G (p + q) y =
          polynomialFunctionTensorRightSlice G p y +
            polynomialFunctionTensorRightSlice G q y by
        simp [polynomialFunctionTensorRightSlice],
        show polynomialFunctionTensor G G (p + q) =
          polynomialFunctionTensor G G p + polynomialFunctionTensor G G q by
        rw [map_add]]
      change polynomialFunctionTensorRightSlice G p y x +
          polynomialFunctionTensorRightSlice G q y x = _
      exact congrArg₂ (· + ·) hp hq

end

/-! Right point slices of coordinate comultiplication are right translates. -/

section

variable {k : Type u} [Field k]

lemma coordinateComultiplication_rightSlice
    (G : Variety k) [AlgebraicGroup G]
    (f : Variety.PolynomialFunction G) (y : Variety.Point G) :
    polynomialFunctionTensorRightSlice G
        (AlgebraicGroup.coordinateComultiplication G f) y =
      (AlgebraicGroup.rightMulMorphism G y).pullbackAlgHom f := by
  apply Variety.PolynomialFunction.ext
  intro x
  rw [polynomialFunctionTensorRightSlice_apply,
    AlgebraicGroup.coordinateComultiplication_apply]
  rfl

end

section
variable {k : Type u} [Field k]

lemma dual_mem_span_polynomialFunctionEvaluation_comp_of_injective
    (G : Variety k) (M : Type v) [AddCommGroup M] [Module k M]
    [FiniteDimensional k M]
    (j : M →ₗ[k] Variety.PolynomialFunction G) (hj : Function.Injective j)
    (K : Module.Dual k M) :
    K ∈ Submodule.span k (Set.range (fun x : Variety.Point G =>
      (polynomialFunctionEvaluationLinearMap G x).comp j)) := by
  refine FiniteDimensional.mem_span_of_iInf_ker_le_ker
    (L := fun x : Variety.Point G =>
      (polynomialFunctionEvaluationLinearMap G x).comp j) ?_
  intro q hq
  have hjqzero : j q = 0 := by
    apply Variety.PolynomialFunction.ext
    intro x
    have hx : q ∈ LinearMap.ker
        ((polynomialFunctionEvaluationLinearMap G x).comp j) :=
      (Submodule.mem_iInf _).1 hq x
    exact LinearMap.mem_ker.mp hx
  have hqzero : q = 0 := hj (by simpa using hjqzero)
  rw [hqzero]
  exact K.map_zero

end

/-! Factoring a tensor through a coordinate subspace from all left slices. -/

section
open scoped TensorProduct

variable {k : Type u} [Field k]

lemma Submodule.exists_tensor_right_of_leftSlices_mem
    (G : Variety k)
    (C : Submodule k (Variety.PolynomialFunction G))
    (z : Variety.PolynomialFunction G ⊗[k] Variety.PolynomialFunction G)
    (hz : ∀ x, polynomialFunctionTensorLeftSlice G z x ∈ C) :
    ∃ w : Variety.PolynomialFunction G ⊗[k] C,
      TensorProduct.map LinearMap.id C.subtype w = z := by
  obtain ⟨U, hUfinite, hzU⟩ :=
    TensorProduct.exists_finite_submodule_left_of_setFinite ({z} : Set _) (Set.finite_singleton z)
  rcases hzU (Set.mem_singleton z) with ⟨w, hw⟩
  let : Module.Finite k U := hUfinite
  have hUfg : U.FG := Submodule.FG.of_finite
  let b := Module.Free.chooseBasis k U
  let c := TensorProduct.equivFinsuppOfBasisLeft b w
  have hc : c.sum (fun i q => b i ⊗ₜ[k] q) = w := by
    exact TensorProduct.equivFinsuppOfBasisLeft_symm_apply b c ▸
      (TensorProduct.equivFinsuppOfBasisLeft b).symm_apply_apply w
  have hcoeff : ∀ i, c i ∈ C := by
    intro i
    obtain ⟨d, hd⟩ := Finsupp.mem_span_range_iff_exists_finsupp.mp
      (Submodule.dual_mem_span_polynomialFunctionEvaluation G U hUfg (b.coord i))
    let coeffMap : Module.Dual k U →ₗ[k] Variety.PolynomialFunction G :=
      { toFun := fun L => TensorProduct.lid k _ ((L.rTensor _) w)
        map_add' := by intro L M; simp
        map_smul' := by intro r L; simp }
    have hci : c i = coeffMap (b.coord i) := by
      change TensorProduct.equivFinsuppOfBasisLeft b w i = _
      rw [TensorProduct.equivFinsuppOfBasisLeft_apply]
      rfl
    rw [hci, ← hd]
    rw [map_finsuppSum]
    apply C.sum_mem
    intro x hx
    change coeffMap ((d x) • polynomialFunctionSubmoduleEvaluation G U x) ∈ C
    rw [coeffMap.map_smul]
    apply C.smul_mem
    have hs : coeffMap (polynomialFunctionSubmoduleEvaluation G U x) =
        polynomialFunctionTensorLeftSlice G z x := by
      have heval : (polynomialFunctionEvaluationLinearMap G x).comp U.subtype =
          polynomialFunctionSubmoduleEvaluation G U x := by
        ext q
        rfl
      change TensorProduct.lid k _
          (((polynomialFunctionSubmoduleEvaluation G U x).rTensor _) w) = _
      rw [← heval, LinearMap.rTensor_comp_apply, hw]
      rfl
    rw [hs]
    exact hz x
  let v : Variety.PolynomialFunction G ⊗[k] C :=
    ∑ i ∈ c.support, (b i).val ⊗ₜ[k] (⟨c i, hcoeff i⟩ : C)
  refine ⟨v, ?_⟩
  rw [← hw, ← hc]
  simp [v, Finsupp.sum]

end

/-! Factoring a tensor through a coordinate subspace from all right slices. -/

section
open scoped TensorProduct

variable {k : Type u} [Field k]

lemma Submodule.exists_tensor_left_of_rightSlices_mem
    (G : Variety k)
    (C : Submodule k (Variety.PolynomialFunction G))
    (z : Variety.PolynomialFunction G ⊗[k] Variety.PolynomialFunction G)
    (hz : ∀ x, polynomialFunctionTensorRightSlice G z x ∈ C) :
    ∃ w : C ⊗[k] Variety.PolynomialFunction G,
      TensorProduct.map C.subtype LinearMap.id w = z := by
  have hcommSlice (p : Variety.PolynomialFunction G ⊗[k]
      Variety.PolynomialFunction G) (x : Variety.Point G) :
      polynomialFunctionTensorLeftSlice G (TensorProduct.comm k _ _ p) x =
        polynomialFunctionTensorRightSlice G p x := by
    induction p with
    | zero =>
        simp [polynomialFunctionTensorLeftSlice,
          polynomialFunctionTensorRightSlice]
    | tmul q r =>
        simp [polynomialFunctionTensorLeftSlice,
          polynomialFunctionTensorRightSlice]
    | add p q hp hq =>
        simpa only [polynomialFunctionTensorLeftSlice,
          polynomialFunctionTensorRightSlice, map_add] using
            congrArg₂ (· + ·) hp hq
  have hslices : ∀ x,
      polynomialFunctionTensorLeftSlice G (TensorProduct.comm k _ _ z) x ∈ C := by
    intro x
    rw [hcommSlice]
    exact hz x
  obtain ⟨w, hw⟩ :=
    Theory.AlgebraicGroup.Submodule.exists_tensor_right_of_leftSlices_mem G C
      (TensorProduct.comm k _ _ z) hslices
  refine ⟨TensorProduct.comm k _ _ w, ?_⟩
  calc
    TensorProduct.map C.subtype LinearMap.id (TensorProduct.comm k _ _ w) =
        TensorProduct.comm k _ _
          (TensorProduct.map LinearMap.id C.subtype w) :=
      TensorProduct.map_comm C.subtype LinearMap.id w
    _ = TensorProduct.comm k _ _ (TensorProduct.comm k _ _ z) := by rw [hw]
    _ = z := by simp

end

/-! Linear extraction of a tensor's right coefficients by dual functionals. -/

section
open scoped TensorProduct

variable {k : Type u} [Field k]

def tensorRightCoefficientMap
    (M : Type v) (N : Type w)
    [AddCommGroup M] [Module k M] [AddCommGroup N] [Module k N]
    (z : M ⊗[k] N) : Module.Dual k N →ₗ[k] M where
  toFun := fun L => TensorProduct.rid k M ((L.lTensor M) z)
  map_add' := by
    intro L K
    simp
  map_smul' := by
    intro r L
    simp

end

section
open scoped TensorProduct
variable {k : Type u} [Field k]

lemma Submodule.exists_tensor_both_of_slices_mem
    (G : Variety k)
    (C : Submodule k (Variety.PolynomialFunction G))
    (z : Variety.PolynomialFunction G ⊗[k] Variety.PolynomialFunction G)
    (hleft : ∀ x, polynomialFunctionTensorLeftSlice G z x ∈ C)
    (hright : ∀ x, polynomialFunctionTensorRightSlice G z x ∈ C) :
    ∃ w : C ⊗[k] C,
      TensorProduct.map C.subtype C.subtype w = z := by
  obtain ⟨w, hw⟩ :=
    Theory.AlgebraicGroup.Submodule.exists_tensor_right_of_leftSlices_mem G C z hleft
  obtain ⟨D, hDfinite, hwD⟩ :=
    TensorProduct.exists_finite_submodule_right_of_setFinite ({w} : Set _) (Set.finite_singleton w)
  rcases hwD (Set.mem_singleton w) with ⟨v, hv⟩
  let : Module.Finite k D := hDfinite
  let : FiniteDimensional k D := hDfinite
  let : Module.Free k D := Module.Free.of_divisionRing k D
  let b := Module.Free.chooseBasis k D
  let c := TensorProduct.equivFinsuppOfBasisRight b v
  have hc : c.sum (fun i q => q ⊗ₜ[k] b i) = v := by
    exact TensorProduct.equivFinsuppOfBasisRight_symm_apply b c ▸
      (TensorProduct.equivFinsuppOfBasisRight b).symm_apply_apply v
  have hcoeff : ∀ i, c i ∈ C := by
    intro i
    let j : D →ₗ[k] Variety.PolynomialFunction G := C.subtype.comp D.subtype
    have hj : Function.Injective j :=
      C.subtype_injective.comp D.subtype_injective
    have hdual := dual_mem_span_polynomialFunctionEvaluation_comp_of_injective
      G D j hj (b.coord i)
    obtain ⟨d, hd⟩ := Finsupp.mem_span_range_iff_exists_finsupp.mp hdual
    let coeffMap := tensorRightCoefficientMap
      (Variety.PolynomialFunction G) D v
    have hci : c i = coeffMap (b.coord i) := by
      change TensorProduct.equivFinsuppOfBasisRight b v i = _
      rw [TensorProduct.equivFinsuppOfBasisRight_apply]
      rfl
    rw [hci, ← hd, map_finsuppSum]
    apply C.sum_mem
    intro x hx
    change coeffMap ((d x) •
      ((polynomialFunctionEvaluationLinearMap G x).comp j)) ∈ C
    rw [coeffMap.map_smul]
    apply C.smul_mem
    have hs : coeffMap
        ((polynomialFunctionEvaluationLinearMap G x).comp j) =
        polynomialFunctionTensorRightSlice G z x := by
      change TensorProduct.rid k _
          (((((polynomialFunctionEvaluationLinearMap G x).comp j)).lTensor _) v) = _
      change TensorProduct.rid k _
          ((((polynomialFunctionEvaluationLinearMap G x).comp
            (C.subtype.comp D.subtype)).lTensor _) v) = _
      rw [LinearMap.lTensor_comp_apply, LinearMap.lTensor_comp_apply, hv]
      have hw' : (C.subtype.lTensor (Variety.PolynomialFunction G)) w = z := by
        exact hw
      rw [hw']
      rfl
    rw [hs]
    exact hright x
  let u : C ⊗[k] C :=
    ∑ i ∈ c.support, (⟨c i, hcoeff i⟩ : C) ⊗ₜ[k] (b i).val
  refine ⟨u, ?_⟩
  rw [← hw, ← hv, ← hc]
  simp [u, Finsupp.sum]

end

/-! Coordinate comultiplication factors through every two-sided translate-stable subalgebra. -/

section
open scoped TensorProduct

variable {k : Type u} [Field k]

public lemma exists_tensorSubalgebra_comultiplication_of_translate_stable
    (G : Variety k) [AlgebraicGroup G]
    (C : Subalgebra k (Variety.PolynomialFunction G))
    (hleft : ∀ a q, q ∈ C →
      (AlgebraicGroup.leftMulMorphism G a).pullbackAlgHom q ∈ C)
    (hright : ∀ b q, q ∈ C →
      (AlgebraicGroup.rightMulMorphism G b).pullbackAlgHom q ∈ C)
    (q : Variety.PolynomialFunction G) (hq : q ∈ C) :
    ∃ w : C ⊗[k] C,
      TensorProduct.map C.toSubmodule.subtype C.toSubmodule.subtype w =
        AlgebraicGroup.coordinateComultiplication G q := by
  apply Theory.AlgebraicGroup.Submodule.exists_tensor_both_of_slices_mem G C.toSubmodule
  · intro x
    rw [AlgebraicGroup.coordinateComultiplication_leftSlice]
    exact hleft x q hq
  · intro y
    rw [AlgebraicGroup.coordinateComultiplication_rightSlice]
    exact hright y q hq

end
end Theory.AlgebraicGroup
