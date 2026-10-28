module

public import Theory.AlgebraicGroup.Instance.SL
public import Theory.AlgebraicGroup.Morphism.ClosedImage

universe u v

/-!
Examples 1.1.7: the tensor representation of `SL(V)` and the resulting
projective special linear group.

For the standard `n`-dimensional model, the matrix of the action on
`V⁺ ⊗ V` in the tensor-product basis is
`(A⁻¹)ᵀ ⊗ A`.  We reindex the pair of matrix indices by
`finProdFinEquiv`, obtaining a polynomial algebraic-group morphism
`SLₙ → SLₙ²`.  Its kernel is exactly the scalar matrices, hence the center
of `SLₙ`.  For an arbitrary finite-dimensional `V`, `PSL(V)` is the image
of this standard morphism with `n = finrank k V`, matching the usual
basis-transported definition.
-/

namespace Theory.AlgebraicGroup

section
open scoped Kronecker

variable {k : Type u} [Field k] [IsAlgClosed k]

/-- The matrix of the natural `SLₙ`-action on the tensor basis of
`(kⁿ)⁺ ⊗ kⁿ`: `(A⁻¹)ᵀ ⊗ A`, reindexed by `Fin (n * n)`. -/
@[expose]
public def slTensorActionMatrix (n : ℕ)
    (A : Matrix.SpecialLinearGroup (Fin n) k) :
    Matrix (Fin (n * n)) (Fin (n * n)) k :=
  Matrix.reindex finProdFinEquiv finProdFinEquiv
    (Matrix.transpose (A⁻¹).1 ⊗ₖ A.1)

omit [IsAlgClosed k] in
/-- The tensor-action matrix has determinant one. -/
public lemma slTensorActionMatrix_det (n : ℕ)
    (A : Matrix.SpecialLinearGroup (Fin n) k) :
    (slTensorActionMatrix n A).det = 1 := by
  rw [slTensorActionMatrix, Matrix.det_reindex_self,
    Matrix.det_kronecker, Matrix.det_transpose]
  rw [(A⁻¹).2, A.2]
  simp

/-- The natural tensor representation on standard special linear groups. -/
@[expose]
public def slTensorActionHom (n : ℕ) :
    Matrix.SpecialLinearGroup (Fin n) k →*
      Matrix.SpecialLinearGroup (Fin (n * n)) k where
  toFun A :=
    ⟨slTensorActionMatrix n A, slTensorActionMatrix_det n A⟩
  map_one' := by
    apply Subtype.ext
    simp [slTensorActionMatrix]
  map_mul' A B := by
    apply Subtype.ext
    change slTensorActionMatrix n (A * B) =
      slTensorActionMatrix n A * slTensorActionMatrix n B
    unfold slTensorActionMatrix
    rw [show ((A * B)⁻¹).1 = (B⁻¹).1 * (A⁻¹).1 by
      simpa only [Matrix.SpecialLinearGroup.coe_mul] using
        congrArg Subtype.val (mul_inv_rev A B)]
    rw [show (A * B).1 = A.1 * B.1 by rfl, Matrix.transpose_mul]
    change (Matrix.reindexAlgEquiv k k finProdFinEquiv)
        ((Matrix.transpose (A⁻¹).1 *
            Matrix.transpose (B⁻¹).1) ⊗ₖ (A.1 * B.1)) =
      (Matrix.reindexAlgEquiv k k finProdFinEquiv)
          (Matrix.transpose (A⁻¹).1 ⊗ₖ A.1) *
        (Matrix.reindexAlgEquiv k k finProdFinEquiv)
          (Matrix.transpose (B⁻¹).1 ⊗ₖ B.1)
    rw [← map_mul]
    rw [← Matrix.mul_kronecker_mul]

omit [IsAlgClosed k] in
@[simp] public lemma slTensorActionMatrix_apply (n : ℕ)
    (A : Matrix.SpecialLinearGroup (Fin n) k)
    (a b i j : Fin n) :
    slTensorActionMatrix n A (finProdFinEquiv (a, b))
        (finProdFinEquiv (i, j)) =
      (A⁻¹).1 i a * A.1 b j := by
  simp [slTensorActionMatrix, Matrix.reindex_apply]

omit [IsAlgClosed k] in
/-- The kernel of the tensor representation is the center of `SLₙ`. -/
public lemma slTensorActionHom_ker (n : ℕ) :
    (slTensorActionHom (k := k) n).ker =
      Subgroup.center (Matrix.SpecialLinearGroup (Fin n) k) := by
  ext A
  constructor
  · intro hA
    by_cases hn : n = 0
    · subst n
      exact Subgroup.mem_center_iff.mpr
        (fun B ↦ Subsingleton.elim _ _)
    · let i₀ : Fin n := ⟨0, Nat.pos_of_ne_zero hn⟩
      let c : k := (A⁻¹).1 i₀ i₀
      have hmatrix : slTensorActionMatrix n A = 1 := by
        exact congrArg Subtype.val hA
      have hdiag (b : Fin n) : c * A.1 b b = 1 := by
        have h := congr_fun
          (congr_fun hmatrix (finProdFinEquiv (i₀, b)))
          (finProdFinEquiv (i₀, b))
        rw [slTensorActionMatrix_apply] at h
        simpa [c] using h
      have hc : c ≠ 0 := by
        intro hc0
        simpa [hc0] using hdiag i₀
      have hoff (b j : Fin n) (hbj : b ≠ j) : A.1 b j = 0 := by
        have h := congr_fun
          (congr_fun hmatrix (finProdFinEquiv (i₀, b)))
          (finProdFinEquiv (i₀, j))
        rw [slTensorActionMatrix_apply] at h
        have hp : (i₀, b) ≠ (i₀, j) := by simp [hbj]
        simp only [Matrix.one_apply,
          finProdFinEquiv.injective.eq_iff, Prod.mk.injEq,
          hbj, and_false, ↓reduceIte] at h
        exact (mul_eq_zero.mp h).resolve_left hc
      have hscalar : Matrix.scalar (Fin n) c⁻¹ = A.1 := by
        ext b j
        by_cases hbj : b = j
        · subst j
          rw [Matrix.scalar_apply, Matrix.diagonal_apply_eq]
          simpa using
            congrArg Inv.inv (eq_inv_of_mul_eq_one_left (hdiag b))
        · simp [Matrix.scalar_apply, hbj, hoff b j hbj]
      rw [Matrix.SpecialLinearGroup.mem_center_iff]
      refine ⟨c⁻¹, ?_, hscalar⟩
      simpa [← hscalar] using A.2
  · intro hA
    rw [Matrix.SpecialLinearGroup.mem_center_iff] at hA
    rcases hA with ⟨r, hr, hscalar⟩
    by_cases hn : n = 0
    · subst n
      apply Subtype.ext
      apply Matrix.ext
      intro i
      exact Fin.elim0 i
    · have hr0 : r ≠ 0 := by
        intro hr0
        have hnpos : 0 < n := Nat.pos_of_ne_zero hn
        simp [hr0, hnpos.ne'] at hr
      have hAAinv : A.1 * (A⁻¹).1 = 1 := by
        simp only [← Matrix.SpecialLinearGroup.coe_mul,
          mul_inv_cancel, Matrix.SpecialLinearGroup.coe_one]
      have hinvA : Matrix.scalar (Fin n) r⁻¹ * A.1 = 1 := by
        rw [← hscalar]
        ext i j
        rw [Matrix.scalar_apply, Matrix.scalar_apply,
          Matrix.one_apply, Matrix.mul_apply]
        by_cases hij : i = j
        · subst j
          rw [if_pos rfl, Finset.sum_eq_single i]
          · simp [hr0]
          · intro b hb hbi
            simp [Matrix.diagonal_apply, hbi]
          · simp
        · rw [if_neg hij]
          apply Finset.sum_eq_zero
          intro b hb
          by_cases hib : i = b
          · subst b
            simp [hij]
          · simp [Matrix.diagonal_apply, hib]
      have hAinv : (A⁻¹).1 = Matrix.scalar (Fin n) r⁻¹ := by
        calc
          (A⁻¹).1 = 1 * (A⁻¹).1 := by rw [one_mul]
          _ = (Matrix.scalar (Fin n) r⁻¹ * A.1) * (A⁻¹).1 := by
            rw [hinvA]
          _ = Matrix.scalar (Fin n) r⁻¹ * (A.1 * (A⁻¹).1) := by
            rw [Matrix.mul_assoc]
          _ = Matrix.scalar (Fin n) r⁻¹ := by
            rw [hAAinv, Matrix.mul_one]
      apply Subtype.ext
      ext p q
      rcases hp : finProdFinEquiv.symm p with ⟨a, b⟩
      rcases hq : finProdFinEquiv.symm q with ⟨i, j⟩
      have hp' : p = finProdFinEquiv (a, b) := by
        simpa [hp] using
          (finProdFinEquiv.apply_symm_apply p).symm
      have hq' : q = finProdFinEquiv (i, j) := by
        simpa [hq] using
          (finProdFinEquiv.apply_symm_apply q).symm
      rw [hp', hq']
      rw [show (slTensorActionHom (k := k) n A).1 =
          slTensorActionMatrix n A by rfl,
        slTensorActionMatrix_apply, hAinv, ← hscalar,
        Matrix.scalar_apply, Matrix.scalar_apply]
      change Matrix.diagonal (fun _ : Fin n ↦ r⁻¹) i a *
          Matrix.diagonal (fun _ : Fin n ↦ r) b j =
        (1 : Matrix (Fin (n * n)) (Fin (n * n)) k)
          (finProdFinEquiv (a, b)) (finProdFinEquiv (i, j))
      by_cases hai : a = i <;> by_cases hbj : b = j <;>
        simp [Matrix.one_apply, finProdFinEquiv.injective.eq_iff,
          Prod.mk.injEq, hai, hbj, eq_comm, hr0]

end

section

open scoped Kronecker

variable {k : Type u} [Field k] [IsAlgClosed k]

/-- The standard point equivalence as a multiplicative equivalence. -/
public noncomputable def slPointMulEquiv (n : ℕ) :
    Variety.Point (slVariety k n) ≃*
      Matrix.SpecialLinearGroup (Fin n) k where
  toEquiv := slPointEquiv n
  map_mul' _ _ := rfl

/-- The multiplicative point equivalence has the same underlying map as the
standard special-linear point equivalence. -/
@[simp] public lemma slPointMulEquiv_apply (n : ℕ)
    (x : Variety.Point (slVariety k n)) :
    slPointMulEquiv n x = slPointEquiv n x := by
  rfl

/-- Coordinate polynomial of the tensor representation. -/
public noncomputable def slTensorActionPolynomial (n : ℕ) :
    (slVariety k (n * n)).Coordinates →
      MvPolynomial (slVariety k n).Coordinates k := fun p ↦
  let ab := finProdFinEquiv.symm p.down.1
  let ij := finProdFinEquiv.symm p.down.2
  slInvPoly n (ULift.up (ij.1, ab.1)) *
    MvPolynomial.X (ULift.up (ab.2, ij.2))

/-- Evaluation of the coordinate polynomial gives the corresponding tensor
action matrix entry. -/
public lemma slTensorActionPolynomial_eval (n : ℕ)
    (x : Variety.Point (slVariety k n))
    (p : (slVariety k (n * n)).Coordinates) :
    evalPolynomial x.val (slTensorActionPolynomial n p) =
      (slTensorActionMatrix n (slPointEquiv n x))
        p.down.1 p.down.2 := by
  rcases p with ⟨⟨p, q⟩⟩
  rcases hp : finProdFinEquiv.symm p with ⟨a, b⟩
  rcases hq : finProdFinEquiv.symm q with ⟨i, j⟩
  have hp' : p = finProdFinEquiv (a, b) := by
    simpa [hp] using (finProdFinEquiv.apply_symm_apply p).symm
  have hq' : q = finProdFinEquiv (i, j) := by
    simpa [hq] using (finProdFinEquiv.apply_symm_apply q).symm
  subst p
  subst q
  rw [slTensorActionMatrix_apply]
  have hinvMatrix : ((slPointEquiv n x)⁻¹).1 =
      Matrix.adjugate (slPointEquiv n x).1 :=
    Matrix.SpecialLinearGroup.coe_inv _
  rw [hinvMatrix]
  simp only [slTensorActionPolynomial,
    finProdFinEquiv.symm_apply_apply]
  change evalPolynomial x.val
      (slInvPoly n (ULift.up (i, a)) *
        MvPolynomial.X (ULift.up (b, j))) =
    Matrix.adjugate (slPointEquiv n x).1 i a *
      (slPointEquiv n x).1 b j
  rw [show evalPolynomial x.val
      (slInvPoly n (ULift.up (i, a)) *
        MvPolynomial.X (ULift.up (b, j))) =
      evalPolynomial x.val (slInvPoly n (ULift.up (i, a))) *
        x.val (ULift.up (b, j)) by simp [evalPolynomial]]
  have hval : (slPointEquiv n x).1 = slPointMatrix n x := rfl
  rw [hval]
  change evalPolynomial x.val
      ((Matrix.adjugate (slEntryMatrix n)) i a) *
        x.val (ULift.up (b, j)) =
    Matrix.adjugate (slPointMatrix n x) i a *
      x.val (ULift.up (b, j))
  rw [evalPolynomial_slAdjugate]
  rw [show slPointMatrix n x =
      (fun i' j' : Fin n ↦ x.val (ULift.up (i', j'))) by rfl]

/-- Example 1.1.7: the polynomial morphism induced by the natural action of
`SLₙ` on `(kⁿ)⁺ ⊗ kⁿ`. -/
@[expose]
public noncomputable def slTensorActionMorphism (n : ℕ) :
    AlgebraicGroup.Morphism (slVariety k n)
      (slVariety k (n * n)) where
  toVariety :=
    { toFun := fun x ↦
        (slPointEquiv (n * n)).symm
          (slTensorActionHom n (slPointEquiv n x))
      regular := fun p ↦
        ⟨slTensorActionPolynomial n p, fun x ↦ by
          change (slTensorActionMatrix n (slPointEquiv n x))
            p.down.1 p.down.2 = _
          exact (slTensorActionPolynomial_eval n x p).symm⟩ }
  map_one := by
    apply (slPointEquiv (n * n)).injective
    change slTensorActionHom n (slPointEquiv n 1) =
      slPointEquiv (n * n) 1
    change slTensorActionHom n 1 = 1
    exact map_one _
  map_mul x y := by
    apply (slPointEquiv (n * n)).injective
    change slTensorActionHom n (slPointEquiv n (x * y)) =
      slPointEquiv (n * n)
        ((slPointEquiv (n * n)).symm
            (slTensorActionHom n (slPointEquiv n x)) *
          (slPointEquiv (n * n)).symm
            (slTensorActionHom n (slPointEquiv n y)))
    change slTensorActionHom n
        (slPointEquiv n x * slPointEquiv n y) =
      slTensorActionHom n (slPointEquiv n x) *
        slTensorActionHom n (slPointEquiv n y)
    exact (slTensorActionHom n).map_mul _ _

@[simp] public lemma slTensorActionMorphism_onPoints (n : ℕ)
    (x : Variety.Point (slVariety k n)) :
    slPointEquiv (n * n)
        ((slTensorActionMorphism (k := k) n).onPoints x) =
      slTensorActionHom n (slPointEquiv n x) := by
  exact (slPointEquiv (n * n)).apply_symm_apply _

/-- The polynomial tensor representation has kernel equal to the center of
the source algebraic group. -/
public lemma slTensorActionMorphism_ker (n : ℕ) :
    (slTensorActionMorphism (k := k) n).kernel =
      Subgroup.center (Variety.Point (slVariety k n)) := by
  ext x
  change (slTensorActionMorphism (k := k) n).onPoints x = 1 ↔
    x ∈ Subgroup.center (Variety.Point (slVariety k n))
  rw [← (slPointEquiv (n * n)).injective.eq_iff]
  rw [slTensorActionMorphism_onPoints]
  change slTensorActionHom n (slPointEquiv n x) = 1 ↔ _
  rw [← MonoidHom.mem_ker, slTensorActionHom_ker]
  change (slPointMulEquiv (k := k) n) x ∈
      Set.center (Matrix.SpecialLinearGroup (Fin n) k) ↔
    x ∈ Set.center (Variety.Point (slVariety k n))
  exact MulEquivClass.apply_mem_center_iff
    (slPointMulEquiv (k := k) n)

end

section

@[expose]
public noncomputable def pslSubgroupOf (k : Type u) [Field k] [IsAlgClosed k]
    (V : Type v) [AddCommGroup V] [Module k V]
    [FiniteDimensional k V] :
    Subgroup (Variety.Point
      (slVariety k (Module.finrank k V * Module.finrank k V))) :=
  (slTensorActionMorphism (k := k) (Module.finrank k V)).image

/-- `PSL(V)` as the closed algebraic subgroup supplied by the closed-image
theorem for the tensor representation. -/
@[expose]
public noncomputable def pslClosedSubgroupOf (k : Type u) [Field k] [IsAlgClosed k]
    (V : Type v) [AddCommGroup V] [Module k V]
    [FiniteDimensional k V] :
    ClosedSubgroup
      (slVariety k (Module.finrank k V * Module.finrank k V)) :=
  (slTensorActionMorphism (k := k) (Module.finrank k V)).imageClosedSubgroup

/-- The underlying subgroup of `pslClosedSubgroupOf` is the tensor-action
image used in `pslSubgroupOf`. -/
public lemma pslClosedSubgroupOf_toSubgroup (k : Type u)
    [Field k] [IsAlgClosed k]
    (V : Type v) [AddCommGroup V] [Module k V]
    [FiniteDimensional k V] :
    (pslClosedSubgroupOf k V).toSubgroup = pslSubgroupOf k V := rfl

public lemma pslClosedSubgroupOf_carrier (k : Type u)
    [Field k] [IsAlgClosed k]
    (V : Type v) [AddCommGroup V] [Module k V]
    [FiniteDimensional k V] :
    ((pslClosedSubgroupOf k V).toSubgroup : Set
      (Variety.Point
        (slVariety k (Module.finrank k V * Module.finrank k V)))) =
      (pslSubgroupOf k V : Set
        (Variety.Point
          (slVariety k (Module.finrank k V * Module.finrank k V)))) := rfl

end

end Theory.AlgebraicGroup
