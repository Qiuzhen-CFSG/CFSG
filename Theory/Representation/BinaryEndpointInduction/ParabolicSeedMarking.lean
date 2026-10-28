module
public import Theory.Representation.BinaryEndpointInduction.CosetLift
public import Theory.Representation.PSL3Two.AutomorphismAction.NaturalDual
public import Theory.GroupTheory.PCoreSurjective

/-!
# The original natural seed in either endpoint orientation

The literal row-e0 stabilizer maps onto SL₃(2) by its lower-right block.
Its block kernel has exponent two. Any surjective marking with kernel O₂
therefore differs from this block map by an actual automorphism of SL₃(2).
The inner and graph possibilities are both retained when changing the seed
coordinates; no innerness assumption is made on the original marking.

Source context: Aschbacher--Smith 15.3.23, binary-four carrier.
-/
public noncomputable section
open Matrix Subgroup Representation
open scoped MatrixGroups
namespace BinaryEndpointInduction
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private theorem fixed_row_mul (A B : Matrix (Fin 4) (Fin 4) (ZMod 2))
    (hA : ∀ k : Fin 4, A 0 k = if k = 0 then 1 else 0) (k : Fin 4) :
    (A * B) 0 k = B 0 k := by
  rw [Matrix.mul_apply,Fin.sum_univ_succ]
  simp only [hA,Fin.succ_ne_zero,ite_true,ite_false,one_mul,zero_mul,
    Finset.sum_const_zero,add_zero]

/-- The exact parabolic used by the right-row coset coordinates. -/
@[expose] def endpointParabolic : Subgroup SL(4,ZMod 2) where
  carrier := {g | ∀ k : Fin 4, g.val 0 k = if k = 0 then 1 else 0}
  one_mem' := by intro k; simp [Matrix.one_apply,eq_comm]
  mul_mem' := by
    intro g h hg hh k
    exact (fixed_row_mul g.val h.val hg k).trans (hh k)
  inv_mem' := by
    intro g hg k
    have he := congrArg (fun a : SL(4,ZMod 2) => a.val 0 k) (mul_inv_cancel g)
    change (g.val * g⁻¹.val) 0 k = (1 : Matrix (Fin 4) (Fin 4) (ZMod 2)) 0 k at he
    rw [fixed_row_mul g.val g⁻¹.val hg k] at he
    simpa only [Matrix.one_apply,eq_comm] using he

/-- All original transition corrections lie in this same literal parabolic. -/
theorem transitionCorrection_mem_endpoint (a : Fin 6) (i : Fin 15) :
    transitionCorrection a i ∈ endpointParabolic := transitionCorrection_row_zero a i

/-- The four displacement actors lie in the same literal parabolic. -/
theorem parabolicGenerator_mem_endpoint (k : Fin 4) :
    parabolicGenerator k ∈ endpointParabolic := parabolicGenerator_row_zero k

private theorem fixed_row_det (A : Matrix (Fin 4) (Fin 4) (ZMod 2))
    (hA : ∀ k : Fin 4, A 0 k = if k = 0 then 1 else 0) :
    A.det = (A.submatrix Fin.succ Fin.succ).det := by
  rw [Matrix.det_succ_row_zero,Fin.sum_univ_succ]
  simp [hA]

private theorem fixed_row_lower_mul (A B : Matrix (Fin 4) (Fin 4) (ZMod 2))
    (hB : ∀ k : Fin 4, B 0 k = if k = 0 then 1 else 0) :
    (A * B).submatrix Fin.succ Fin.succ =
      A.submatrix Fin.succ Fin.succ * B.submatrix Fin.succ Fin.succ := by
  ext i k
  change (∑ u : Fin 4, A i.succ u * B u k.succ) =
    ∑ u : Fin 3, A i.succ u.succ * B u.succ k.succ
  rw [Fin.sum_univ_succ]
  simp [hB]

/-- Expansion along the fixed first row retains the lower-right determinant. -/
theorem endpoint_lower_det (g : endpointParabolic) :
    (g.val.val.submatrix Fin.succ Fin.succ).det = 1 :=
  (fixed_row_det g.val.val g.property).symm.trans g.val.property

/-- The canonical lower-right quotient, with its literal matrix entries. -/
@[expose] def endpointLevi : endpointParabolic →* SL(3,ZMod 2) where
  toFun g := ⟨g.val.val.submatrix Fin.succ Fin.succ,endpoint_lower_det g⟩
  map_one' := by apply Subtype.ext; ext i j; simp [Matrix.submatrix,Matrix.one_apply]
  map_mul' g h := by
    apply Subtype.ext
    exact fixed_row_lower_mul g.val.val h.val.val h.property

private def diagonalLiftMatrix (g : SL(3,ZMod 2)) : Matrix (Fin 4) (Fin 4) (ZMod 2) :=
  fun i k => Fin.cases (if k = 0 then 1 else 0)
    (fun i => Fin.cases 0 (fun k => g.val i k) k) i

private theorem diagonalLift_det (g : SL(3,ZMod 2)) : (diagonalLiftMatrix g).det = 1 := by
  rw [Matrix.det_succ_row_zero,Fin.sum_univ_succ]
  simp only [diagonalLiftMatrix,Fin.cases_zero,Fin.succ_ne_zero,ite_true,ite_false,
    mul_zero,zero_mul,Finset.sum_const_zero,add_zero,Fin.val_zero,pow_zero,one_mul,Fin.succAbove_zero]
  change g.val.det = 1
  exact g.property

/-- Every actual three-dimensional determinant-one block occurs. -/
theorem endpointLevi_surjective : Function.Surjective endpointLevi := by
  intro g
  let a : SL(4,ZMod 2) := ⟨diagonalLiftMatrix g,diagonalLift_det g⟩
  have ha : a ∈ endpointParabolic := by intro k; rfl
  refine ⟨⟨a,ha⟩,?_⟩
  apply Subtype.ext
  ext i k
  rfl

private theorem fixed_row_lower_one_square (A : Matrix (Fin 4) (Fin 4) (ZMod 2))
    (hA : ∀ k : Fin 4, A 0 k = if k = 0 then 1 else 0)
    (hD : A.submatrix Fin.succ Fin.succ = 1) : A * A = 1 := by
  have hd (i k : Fin 3) : A i.succ k.succ = if i = k then 1 else 0 := by
    have he := congrArg (fun B : Matrix (Fin 3) (Fin 3) (ZMod 2) => B i k) hD
    simpa only [Matrix.submatrix_apply,Matrix.one_apply] using he
  ext i k
  refine Fin.cases ?_ (fun i => ?_) i
  · simp [Matrix.mul_apply,hA,Matrix.one_apply,eq_comm]
  · refine Fin.cases ?_ (fun k => ?_) k
    · simp [Matrix.mul_apply,Fin.sum_univ_succ,hA,hd,CharTwo.add_self_eq_zero]
    · simp [Matrix.mul_apply,Fin.sum_univ_succ,hA,hd,Matrix.one_apply]

private theorem endpoint_kernel_square (g : endpointParabolic) (hg : endpointLevi g = 1) :
    g ^ 2 = 1 := by
  rw [pow_two]
  apply Subtype.ext
  apply Subtype.ext
  exact fixed_row_lower_one_square g.val.val g.property
    (congrArg (fun a : SL(3,ZMod 2) => a.val) hg)

/-- The canonical block kernel is an actual two-group. -/
theorem endpointLevi_kernel_two : IsPGroup 2 endpointLevi.ker := by
  rw [isPGroup_iff_pow_pow_eq_one]
  intro g
  refine ⟨1,?_⟩
  apply Subtype.ext
  exact endpoint_kernel_square g.val g.property

private theorem marking_factor
    (β : endpointParabolic →* SL(3,ZMod 2)) (hβ : Function.Surjective β)
    (hker : β.ker = pCore 2 endpointParabolic) :
    ∃ α : MulAut SL(3,ZMod 2), ∀ p : endpointParabolic, β p = α (endpointLevi p) := by
  have hk : endpointLevi.ker ≤ β.ker := by
    rw [hker]
    exact le_sSup ⟨inferInstance,endpointLevi_kernel_two⟩
  let e := QuotientGroup.quotientKerEquivOfSurjective endpointLevi endpointLevi_surjective
  let f := (QuotientGroup.lift endpointLevi.ker β hk).comp e.symm.toMonoidHom
  have hf (p : endpointParabolic) : f (endpointLevi p) = β p := by
    change QuotientGroup.lift endpointLevi.ker β hk
      (e.symm (e (QuotientGroup.mk' endpointLevi.ker p))) = β p
    rw [e.symm_apply_apply]
    rfl
  have hs : Function.Surjective f := by
    intro y
    obtain ⟨p,rfl⟩ := hβ y
    exact ⟨endpointLevi p,hf p⟩
  exact ⟨MulEquiv.ofBijective f ⟨(Finite.injective_iff_surjective).mpr hs,hs⟩,fun p => (hf p).symm⟩

private theorem true_block_transpose (a : Fin 6) (i : Fin 15) :
    (transitionBlock true a i).transpose =
      (endpointLevi ⟨transitionCorrection a i,transitionCorrection_mem_endpoint a i⟩)⁻¹.val := by
  let p : endpointParabolic := ⟨transitionCorrection a i,transitionCorrection_mem_endpoint a i⟩
  let d := endpointLevi p
  have hd : transitionBlock false a i = d.val := transitionBlock_false a i
  have he := congrArg Matrix.transpose (transitionBlock_inverseTranspose a i).1
  have he' : d.val * (transitionBlock true a i).transpose = 1 := by
    simpa only [Matrix.transpose_mul,Matrix.transpose_transpose,Matrix.transpose_one,hd] using he
  have hi : d⁻¹.val * d.val = 1 := by
    exact congrArg (fun g : SL(3,ZMod 2) => g.val) (inv_mul_cancel d)
  calc
    (transitionBlock true a i).transpose =
        (d⁻¹.val * d.val) * (transitionBlock true a i).transpose := by rw [hi,one_mul]
    _ = d⁻¹.val := by rw [mul_assoc,he',mul_one]

private theorem seed_conjugate_action
    {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    (τ : Representation (ZMod 2) SL(4,ZMod 2) W)
    (β : endpointParabolic →* SL(3,ZMod 2))
    (j : (Fin 3 → ZMod 2) →ₗ[ZMod 2] W)
    (haction : ∀ (p : endpointParabolic) (v : Fin 3 → ZMod 2),
      τ p.val (j v) = j ((β p).val *ᵥ v))
    (p : endpointParabolic) (g d : SL(3,ZMod 2))
    (hp : β p⁻¹ = g * d * g⁻¹) (v : Fin 3 → ZMod 2) :
    τ p.val⁻¹ (j (g.toLin' v)) = j (g.toLin' (d.toLin' v)) := by
  rw [show p.val⁻¹ = (p⁻¹).val from rfl,haction]
  apply congrArg j
  change (β p⁻¹).toLin' (g.toLin' v) = _
  rw [hp,map_mul,map_mul]
  simp only [LinearEquiv.mul_apply,map_inv,LinearEquiv.coe_inv,LinearEquiv.symm_apply_apply]

/-- An arbitrary genuine natural marking supplies one of the two exact
local coefficient systems. The invertible seed change preserves its image;
the graph automorphism possibility is retained, rather than assumed inner. -/
theorem exists_seed_marking
    {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    (τ : Representation (ZMod 2) SL(4,ZMod 2) W)
    (β : endpointParabolic →* SL(3,ZMod 2)) (hβ : Function.Surjective β)
    (hker : β.ker = pCore 2 endpointParabolic)
    (j : (Fin 3 → ZMod 2) →ₗ[ZMod 2] W)
    (haction : ∀ (p : endpointParabolic) (v : Fin 3 → ZMod 2),
      τ p.val (j v) = j ((β p).val *ᵥ v)) :
    ∃ (dual : Bool) (e : (Fin 3 → ZMod 2) ≃ₗ[ZMod 2] (Fin 3 → ZMod 2)),
      LinearMap.range (j.comp e.toLinearMap) = LinearMap.range j ∧
      ∀ (a : Fin 6) (i : Fin 15) (v : Fin 3 → ZMod 2),
        (j.comp e.toLinearMap) (v ᵥ* transitionBlock dual a i) =
          τ (transitionCorrection a i)⁻¹ ((j.comp e.toLinearMap) v) := by
  obtain ⟨α,hα⟩ := marking_factor β hβ hker
  by_cases hi : α ∈ MulAut.innerSubgroup SL(3,ZMod 2)
  · obtain ⟨g,hg⟩ := hi
    refine ⟨true,g.toLin',?_,?_⟩
    · exact LinearMap.range_comp_of_range_eq_top j
        (LinearMap.range_eq_top.mpr g.toLin'.surjective)
    · intro a i v
      let p : endpointParabolic := ⟨transitionCorrection a i,transitionCorrection_mem_endpoint a i⟩
      have hp : β p⁻¹ = g * (endpointLevi p)⁻¹ * g⁻¹ := by
        rw [hα,map_inv,← hg]
        rfl
      have hv : v ᵥ* transitionBlock true a i = (endpointLevi p)⁻¹.toLin' v := by
        rw [← Matrix.mulVec_transpose,true_block_transpose]
        rfl
      change j (g.toLin' (v ᵥ* transitionBlock true a i)) = τ p.val⁻¹ (j (g.toLin' v))
      rw [hv]
      exact (seed_conjugate_action τ β j haction p g _ hp v).symm
  · obtain ⟨g,hg⟩ := BinaryLinearThree.AutomorphismAction.outer_eq_inner_graph α hi
    refine ⟨false,g.toLin',?_,?_⟩
    · exact LinearMap.range_comp_of_range_eq_top j
        (LinearMap.range_eq_top.mpr g.toLin'.surjective)
    · intro a i v
      let p : endpointParabolic := ⟨transitionCorrection a i,transitionCorrection_mem_endpoint a i⟩
      have hp : β p⁻¹ = g * (endpointLevi p).transpose * g⁻¹ := by
        rw [hα,map_inv,hg]
        simp only [MulAut.mul_apply,MulAut.conj_apply,
          BinaryLinearThree.AutomorphismAction.graph_apply,inv_inv]
      have hv : v ᵥ* transitionBlock false a i = (endpointLevi p).transpose.toLin' v := by
        change v ᵥ* transitionBlock false a i = (endpointLevi p).val.transpose *ᵥ v
        rw [Matrix.mulVec_transpose,transitionBlock_false]
        rfl
      change j (g.toLin' (v ᵥ* transitionBlock false a i)) = τ p.val⁻¹ (j (g.toLin' v))
      rw [hv]
      exact (seed_conjugate_action τ β j haction p g _ hp v).symm

end BinaryEndpointInduction
