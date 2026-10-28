module

public import Theory.AlgebraicGroup.Borel.GeometricConjugacy.CompleteModel.FlagGeometry.ClosedImage.Annihilator
public import Theory.AlgebraicGroup.Borel.GeometricConjugacy.CompleteModel.FlagGeometry.ClosedImage.DeterminantalLocus.MatrixRank

/-!
# Bihomogeneous equations for simultaneous wedge kernels

The entries of `v ↦ ι(v) * a` are linear functions of the exterior vector `a`.
Writing those functions in arbitrary bases gives a polynomial matrix for a pair
of stacked wedge maps. Its minors are homogeneous for the two-block grading:
the bidegree is the sum of the weights of the selected rows. Evaluation recovers
the actual linear maps, so the equations are equivalent to their rank bounds.

No decomposability is used. In particular the same construction applies to two
independent copies of one exterior degree; diagonal flag conditions are obtained
by pulling back along the diagonal. This is the determinantal algebra underlying
the flag-variety construction used in Borel, *Linear Algebraic Groups*, §11.1.
Scheme-theoretic closedness of these equations is a separate geometric step.
-/

@[expose] public noncomputable section

open scoped ExteriorAlgebra
open Module MvPolynomial

namespace Theory.AlgebraicGroup.BorelGeometricConjugacy.FlagGeometry.DeterminantalLocus

universe u v
variable {k : Type u} [Field k] {V : Type v} [AddCommGroup V] [Module k V]

/-- Left multiplication by a fixed vector, linear in the exterior argument. -/
def wedgeInExterior {d : ℕ} (v : V) : (⋀[k]^d V) →ₗ[k] ⋀[k]^(d+1) V where
  toFun a := wedgeVectorMap a v
  map_add' a b := by
    apply Subtype.ext
    simp only [wedgeVectorMap_coe, Submodule.coe_add, mul_add]
  map_smul' c a := by
    apply Subtype.ext
    simp only [wedgeVectorMap_coe, Submodule.coe_smul, Algebra.mul_smul_comm,
      RingHom.id_apply]

variable {σ τ ι γ δ : Type*} [Fintype σ]

/-- The polynomial of a linear functional, with its variables relabelled by `f`. -/
def coordinateLinearPolynomial {E : Type*} [AddCommGroup E] [Module k E]
    (b : Basis σ k E) (l : E →ₗ[k] k) (f : σ → τ) : MvPolynomial τ k :=
  ∑ i, C (l (b i)) * X (f i)

/-- Evaluating a coordinate linear polynomial recovers the original functional. -/
theorem coordinateLinearPolynomial_eval {E : Type*} [AddCommGroup E] [Module k E]
    (b : Basis σ k E) (l : E →ₗ[k] k) (f : σ → τ)
    (x : τ → k) (a : E) (ha : ∀ i, x (f i) = b.repr a i) :
    eval x (coordinateLinearPolynomial b l f) = l a := by
  simp only [coordinateLinearPolynomial, map_sum, map_mul, eval_C, eval_X, ha]
  conv_rhs => rw [← b.sum_repr a]
  simp only [map_sum, map_smul, smul_eq_mul]
  exact Finset.sum_congr rfl (fun _ _ => mul_comm _ _)

/-- A linear polynomial has the common weight of its variables. -/
theorem coordinateLinearPolynomial_homogeneous
    {E : Type*} [AddCommGroup E] [Module k E]
    {D : Type*} [AddCommMonoid D] (b : Basis σ k E) (l : E →ₗ[k] k)
    (f : σ → τ) (w : τ → D) (d : D) (hf : ∀ i, w (f i) = d) :
    (coordinateLinearPolynomial b l f).IsWeightedHomogeneous w d := by
  apply IsWeightedHomogeneous.sum
  intro i _
  exact (hf i ▸ isWeightedHomogeneous_X k w (f i)).C_mul (l (b i))

/-- The two independent projective-coordinate weights. -/
def blockWeight {σ τ : Type*} : σ ⊕ τ → ℕ × ℕ :=
  Sum.elim (fun _ => (1, 0)) (fun _ => (0, 1))

/-- If every entry in row `i` has weight `d i`, the determinant has weight `∑ i, d i`. -/
theorem det_weightedHomogeneous {s : Type*} [Fintype s] [DecidableEq s]
    {D : Type*} [AddCommMonoid D] (w : τ → D) (d : s → D)
    (A : Matrix s s (MvPolynomial τ k))
    (hA : ∀ i j, (A i j).IsWeightedHomogeneous w (d i)) :
    A.det.IsWeightedHomogeneous w (∑ i, d i) := by
  rw [← Matrix.det_transpose, Matrix.det_apply]
  apply IsWeightedHomogeneous.sum
  intro p _
  have hp := IsWeightedHomogeneous.prod Finset.univ
    (fun i => A i (p i)) d (fun i _ => hA i (p i))
  change _ ∈ weightedHomogeneousSubmodule k w (∑ i, d i)
  change (p.sign : ℤ) • (∏ i, A i (p i)) ∈ _
  exact
    (weightedHomogeneousSubmodule k w (∑ i, d i)).toAddSubgroup.zsmul_mem hp
      (p.sign : ℤ)

variable {d e : ℕ} [Fintype τ]

/-- The actual stacked wedge matrix with universal exterior coordinates. -/
def wedgeMatrixPolynomial (bv : Basis ι k V)
    (bd : Basis σ k (⋀[k]^d V)) (be : Basis τ k (⋀[k]^e V))
    (cd : Basis γ k (⋀[k]^(d+1) V)) (ce : Basis δ k (⋀[k]^(e+1) V)) :
    Matrix (γ ⊕ δ) ι (MvPolynomial (σ ⊕ τ) k)
  | .inl r, j => coordinateLinearPolynomial bd
      ((cd.coord r).comp (wedgeInExterior (bv j))) Sum.inl
  | .inr r, j => coordinateLinearPolynomial be
      ((ce.coord r).comp (wedgeInExterior (bv j))) Sum.inr

/-- An entry is linear in precisely the exterior-coordinate block of its row. -/
theorem wedgeMatrixPolynomial_homogeneous (bv : Basis ι k V)
    (bd : Basis σ k (⋀[k]^d V)) (be : Basis τ k (⋀[k]^e V))
    (cd : Basis γ k (⋀[k]^(d+1) V)) (ce : Basis δ k (⋀[k]^(e+1) V))
    (r : γ ⊕ δ) (j : ι) :
    (wedgeMatrixPolynomial bv bd be cd ce r j).IsWeightedHomogeneous
      blockWeight (blockWeight r) := by
  cases r with
  | inl r => exact coordinateLinearPolynomial_homogeneous _ _ _ _ _ (fun _ => rfl)
  | inr r => exact coordinateLinearPolynomial_homogeneous _ _ _ _ _ (fun _ => rfl)

/-- Evaluation gives the matrix of the two actual wedge maps in the chosen bases. -/
theorem wedgeMatrixPolynomial_eval [Fintype ι] [DecidableEq ι] [Fintype γ] [Fintype δ] (bv : Basis ι k V)
    (bd : Basis σ k (⋀[k]^d V)) (be : Basis τ k (⋀[k]^e V))
    (cd : Basis γ k (⋀[k]^(d+1) V)) (ce : Basis δ k (⋀[k]^(e+1) V))
    (a : ⋀[k]^d V) (b : ⋀[k]^e V) :
    (wedgeMatrixPolynomial bv bd be cd ce).map
      (eval (Sum.elim (bd.equivFun a) (be.equivFun b))) =
      LinearMap.toMatrix bv (cd.prod ce) ((wedgeVectorMap a).prod (wedgeVectorMap b)) := by
  ext r j
  cases r with
  | inl r =>
    simpa only [Matrix.map_apply, wedgeMatrixPolynomial, LinearMap.toMatrix_apply,
      Basis.prod_repr_inl, LinearMap.prod_apply, Function.prod, LinearMap.comp_apply,
      Basis.coord_apply, wedgeInExterior, LinearMap.coe_mk, AddHom.coe_mk] using
      coordinateLinearPolynomial_eval bd ((cd.coord r).comp (wedgeInExterior (bv j)))
        Sum.inl (Sum.elim (bd.equivFun a) (be.equivFun b)) a (fun _ => rfl)
  | inr r =>
    simpa only [Matrix.map_apply, wedgeMatrixPolynomial, LinearMap.toMatrix_apply,
      Basis.prod_repr_inr, LinearMap.prod_apply, Function.prod, LinearMap.comp_apply,
      Basis.coord_apply, wedgeInExterior, LinearMap.coe_mk, AddHom.coe_mk] using
      coordinateLinearPolynomial_eval be ((ce.coord r).comp (wedgeInExterior (bv j)))
        Sum.inr (Sum.elim (bd.equivFun a) (be.equivFun b)) b (fun _ => rfl)

/-- A fixed minor of the universal stacked wedge matrix. -/
def wedgeMinorPolynomial (bv : Basis ι k V)
    (bd : Basis σ k (⋀[k]^d V)) (be : Basis τ k (⋀[k]^e V))
    (cd : Basis γ k (⋀[k]^(d+1) V)) (ce : Basis δ k (⋀[k]^(e+1) V))
    {q : ℕ} (r : Fin q → γ ⊕ δ) (c : Fin q → ι) : MvPolynomial (σ ⊕ τ) k :=
  ((wedgeMatrixPolynomial bv bd be cd ce).submatrix r c).det

/-- The bidegree of a minor counts its selected rows in each block. -/
theorem wedgeMinorPolynomial_homogeneous (bv : Basis ι k V)
    (bd : Basis σ k (⋀[k]^d V)) (be : Basis τ k (⋀[k]^e V))
    (cd : Basis γ k (⋀[k]^(d+1) V)) (ce : Basis δ k (⋀[k]^(e+1) V))
    {q : ℕ} (r : Fin q → γ ⊕ δ) (c : Fin q → ι) :
    (wedgeMinorPolynomial bv bd be cd ce r c).IsWeightedHomogeneous
      blockWeight (∑ i, blockWeight (r i)) :=
  det_weightedHomogeneous _ _ _ (fun i j =>
    wedgeMatrixPolynomial_homogeneous bv bd be cd ce (r i) (c j))

/-- The polynomial minor evaluates to the corresponding numerical minor. -/
theorem wedgeMinorPolynomial_eval [Fintype ι] [DecidableEq ι] [Fintype γ] [Fintype δ]
    (bv : Basis ι k V)
    (bd : Basis σ k (⋀[k]^d V)) (be : Basis τ k (⋀[k]^e V))
    (cd : Basis γ k (⋀[k]^(d+1) V)) (ce : Basis δ k (⋀[k]^(e+1) V))
    (a : ⋀[k]^d V) (b : ⋀[k]^e V)
    {q : ℕ} (r : Fin q → γ ⊕ δ) (c : Fin q → ι) :
    eval (Sum.elim (bd.equivFun a) (be.equivFun b))
      (wedgeMinorPolynomial bv bd be cd ce r c) =
      ((LinearMap.toMatrix bv (cd.prod ce)
        ((wedgeVectorMap a).prod (wedgeVectorMap b))).submatrix r c).det := by
  rw [wedgeMinorPolynomial, RingHom.map_det]
  change (((wedgeMatrixPolynomial bv bd be cd ce).map
    (eval (Sum.elim (bd.equivFun a) (be.equivFun b)))).submatrix r c).det = _
  rw [wedgeMatrixPolynomial_eval]

/-- The explicit polynomial equations are equivalent to the stacked wedge rank bound. -/
theorem stacked_rank_iff_minorEquations
    [Fintype ι] [DecidableEq ι] [Fintype γ] [Fintype δ]
    (bv : Basis ι k V)
    (bd : Basis σ k (⋀[k]^d V)) (be : Basis τ k (⋀[k]^e V))
    (cd : Basis γ k (⋀[k]^(d+1) V)) (ce : Basis δ k (⋀[k]^(e+1) V))
    (a : ⋀[k]^d V) (b : ⋀[k]^e V) (t : ℕ) :
    Module.finrank k (LinearMap.range
      ((wedgeVectorMap a).prod (wedgeVectorMap b))) ≤ t ↔
      ∀ (r : Fin (t+1) → γ ⊕ δ) (c : Fin (t+1) → ι),
        eval (Sum.elim (bd.equivFun a) (be.equivFun b))
          (wedgeMinorPolynomial bv bd be cd ce r c) = 0 := by
  simp_rw [wedgeMinorPolynomial_eval]
  rw [← rank_le_iff_minors, Matrix.rank_eq_finrank_range_toLin _ (cd.prod ce) bv,
    Matrix.toLin_toMatrix]

end Theory.AlgebraicGroup.BorelGeometricConjugacy.FlagGeometry.DeterminantalLocus
