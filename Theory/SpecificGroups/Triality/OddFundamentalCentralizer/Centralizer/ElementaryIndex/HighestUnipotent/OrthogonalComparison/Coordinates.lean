module
public import Theory.SpecificGroups.Triality.OddFundamentalCentralizer.Centralizer.ElementaryIndex.HighestUnipotent.OrthogonalComparison.Integral

/-!
# Faithful odd-characteristic adjoint coordinates

Specialize the signed integral columns and recover twice every original
coordinate from the resulting eight-by-eight matrix. This proves injectivity
whenever two is nonzero. Both actual Geck simple-root curves intertwine with
conjugation by the specified natural root matrices; there is no quotient,
generation, or model-comparison hypothesis in these identities.

Sources: GLS3 §§2.4, 2.6–2.7; Aschbacher–Smith A.2.17, printed pp.38–39.
-/

set_option backward.isDefEq.respectTransparency false

@[expose] public section
noncomputable section
open Matrix
namespace Triality.Standard.OddFundamentalCentralizer.ElementaryIndex.HighestUnipotent.OrthogonalComparison
open Geometry.Integral

theorem integral_linear (i : Fin 4) (d : Bool) (c : Ix) (a b : NaturalIndex) :
    (∑ k, matrix (linear i d) k c * basisMatrix k a b) =
      (naturalGenerator i d * basisMatrix c - basisMatrix c * naturalGenerator i d) a b := by
  calc
    _ = rowProduct (coordinateRows a b) (linear i d) c := by
      rw [← rowEntry_mul]
      apply Finset.sum_congr rfl
      intro k _
      exact mul_comm _ _
    _ = _ := by
      rw [(coefficient_identity i d a b c).1, leftEntry_eq, rightEntry_eq]
      rfl

theorem integral_quadratic (i : Fin 4) (d : Bool) (c : Ix) (a b : NaturalIndex) :
    (∑ k, matrix (quadratic i d) k c * basisMatrix k a b) =
      (-(naturalGenerator i d * basisMatrix c * naturalGenerator i d)) a b := by
  calc
    _ = rowProduct (coordinateRows a b) (quadratic i d) c := by
      rw [← rowEntry_mul]
      apply Finset.sum_congr rfl
      intro k _
      exact mul_comm _ _
    _ = _ := by
      rw [(coefficient_identity i d a b c).2, rightEntry_eq, leftEntry_eq]
      rfl


section Specialization
variable (R : Type*) [CommRing R]

def castMatrix : NaturalMatrix ℤ →+* NaturalMatrix R := (Int.castRingHom R).mapMatrix

def embedding : (Ix → R) →ₗ[R] NaturalMatrix R where
  toFun v := ∑ c, v c • castMatrix R (basisMatrix c)
  map_add' v w := by simp [add_smul, Finset.sum_add_distrib]
  map_smul' t v := by simp [mul_smul, Finset.smul_sum]

def sparseEval (l : List (Ix × ℤ)) (v : Ix → R) : R :=
  (l.map fun p => v p.1 * (p.2 : R)).sum

private theorem eval_rowEntry (l : List (Ix × ℤ)) (v : Ix → R) :
    (∑ c, v c * (rowEntry l c : R)) = sparseEval R l v := by
  induction l with
  | nil => simp [rowEntry, sparseEval]
  | cons p l ih =>
    rcases p with ⟨k,a⟩
    simp [rowEntry, sparseEval, mul_add, Finset.sum_add_distrib, ih, mul_ite]

theorem embedding_apply (v : Ix → R) (a b : NaturalIndex) :
    embedding R v a b = sparseEval R (coordinateRows a b) v := by
  change (∑ c, v c • castMatrix R (basisMatrix c)) a b = _
  simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
  exact eval_rowEntry R _ v

theorem embedding_single (c : Ix) :
    embedding R (Pi.single c 1) = castMatrix R (basisMatrix c) := by
  classical
  simp [embedding, Pi.single_apply, ite_smul]

private theorem embedding_mulVec_of_columns
    (A : Matrix Ix Ix R) (L : NaturalMatrix R →ₗ[R] NaturalMatrix R)
    (h : ∀ c, ∑ k, A k c • castMatrix R (basisMatrix k) =
      L (castMatrix R (basisMatrix c))) (v : Ix → R) :
    embedding R (A *ᵥ v) = L (embedding R v) := by
  change (∑ k, (∑ c, A k c * v c) • castMatrix R (basisMatrix k)) =
    L (∑ c, v c • castMatrix R (basisMatrix c))
  simp only [Finset.sum_smul, map_sum, map_smul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro c _
  rw [← h c, Finset.smul_sum]
  simp only [smul_smul, mul_comm]

private theorem linear_specialization (i : Fin 4) (d : Bool) (c : Ix) :
    (∑ k, Geometry.specialize (F := R) (matrix (linear i d)) k c • castMatrix R (basisMatrix k)) =
      castMatrix R (naturalGenerator i d) * castMatrix R (basisMatrix c) -
        castMatrix R (basisMatrix c) * castMatrix R (naturalGenerator i d) := by
  rw [← map_mul, ← map_mul, ← map_sub]
  ext a b
  simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
  change (∑ k, (matrix (linear i d) k c : R) * (basisMatrix k a b : R)) =
    ((naturalGenerator i d * basisMatrix c - basisMatrix c * naturalGenerator i d) a b : R)
  simpa only [Int.cast_sum, Int.cast_mul] using
    congrArg (fun z : ℤ => (z : R)) (integral_linear i d c a b)

private theorem quadratic_specialization (i : Fin 4) (d : Bool) (c : Ix) :
    (∑ k, Geometry.specialize (F := R) (matrix (quadratic i d)) k c • castMatrix R (basisMatrix k)) =
      -(castMatrix R (naturalGenerator i d) * castMatrix R (basisMatrix c) *
        castMatrix R (naturalGenerator i d)) := by
  rw [← map_mul, ← map_mul, ← map_neg]
  ext a b
  simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
  change (∑ k, (matrix (quadratic i d) k c : R) * (basisMatrix k a b : R)) =
    ((-(naturalGenerator i d * basisMatrix c * naturalGenerator i d)) a b : R)
  simpa only [Int.cast_sum, Int.cast_mul] using
    congrArg (fun z : ℤ => (z : R)) (integral_quadratic i d c a b)

theorem embedding_linear (i : Fin 4) (d : Bool) (v : Ix → R) :
    embedding R (Geometry.specialize (matrix (linear i d)) *ᵥ v) =
      castMatrix R (naturalGenerator i d) * embedding R v -
        embedding R v * castMatrix R (naturalGenerator i d) :=
  embedding_mulVec_of_columns R _
    (LinearMap.mulLeft R (castMatrix R (naturalGenerator i d)) -
      LinearMap.mulRight R (castMatrix R (naturalGenerator i d)))
    (linear_specialization R i d) v

theorem embedding_quadratic (i : Fin 4) (d : Bool) (v : Ix → R) :
    embedding R (Geometry.specialize (matrix (quadratic i d)) *ᵥ v) =
      -(castMatrix R (naturalGenerator i d) * embedding R v *
        castMatrix R (naturalGenerator i d)) :=
  embedding_mulVec_of_columns R _
    (-((LinearMap.mulRight R (castMatrix R (naturalGenerator i d))).comp
      (LinearMap.mulLeft R (castMatrix R (naturalGenerator i d)))))
    (quadratic_specialization R i d) v

def naturalCurve (i : Fin 4) (d : Bool) (t : R) : NaturalMatrix R :=
  1 + t • castMatrix R (naturalGenerator i d)

theorem curve_intertwines (i : Fin 4) (d : Bool) (t : R) (v : Ix → R) :
    naturalCurve R i d t * embedding R v * naturalCurve R i d (-t) =
      embedding R (Geometry.curve i d t *ᵥ v) := by
  rw [Geometry.curve, Matrix.add_mulVec, Matrix.add_mulVec, Matrix.one_mulVec,
    Matrix.smul_mulVec, Matrix.smul_mulVec, map_add, map_add, map_smul, map_smul,
    embedding_linear, embedding_quadratic]
  simp only [naturalCurve, add_mul, mul_add, one_mul, mul_one,
    Matrix.smul_mul, Matrix.mul_smul, smul_sub, smul_neg,
    smul_smul, neg_smul, mul_neg, pow_two]
  abel

def recover (M : NaturalMatrix R) : Ix → R :=
  ![2 * M (.inl 0) (.inl 0),
    -2 * M (.inl 1) (.inl 1) - 2 * M (.inl 0) (.inl 0),
    M (.inl 2) (.inl 2) + M (.inl 1) (.inl 1) + M (.inl 0) (.inl 0) - M (.inl 3) (.inl 3),
    M (.inl 2) (.inl 2) + M (.inl 1) (.inl 1) + M (.inl 0) (.inl 0) + M (.inl 3) (.inl 3),
    -2 * M (.inl 0) (.inr 1),
    -2 * M (.inl 0) (.inl 1),
    2 * M (.inl 1) (.inl 0),
    -2 * M (.inr 0) (.inl 1),
    -2 * M (.inl 0) (.inr 2),
    2 * M (.inl 0) (.inl 2),
    2 * M (.inl 2) (.inl 0),
    2 * M (.inr 0) (.inl 2),
    -2 * M (.inl 0) (.inr 3),
    -2 * M (.inl 0) (.inl 3),
    2 * M (.inl 3) (.inl 0),
    -2 * M (.inr 0) (.inl 3),
    -2 * M (.inl 1) (.inr 2),
    2 * M (.inl 1) (.inl 2),
    -2 * M (.inl 2) (.inl 1),
    -2 * M (.inr 1) (.inl 2),
    -2 * M (.inl 1) (.inr 3),
    -2 * M (.inl 1) (.inl 3),
    -2 * M (.inl 3) (.inl 1),
    2 * M (.inr 1) (.inl 3),
    -2 * M (.inl 2) (.inr 3),
    -2 * M (.inl 2) (.inl 3),
    2 * M (.inl 3) (.inl 2),
    -2 * M (.inr 2) (.inl 3)]

theorem recover_embedding (v : Ix → R) : recover R (embedding R v) = (2 : R) • v := by
  funext c
  fin_cases c <;>
    simp [recover, embedding_apply, coordinateRows, sparseEval, finSumFinEquiv, Fin.castAdd, Fin.natAdd] <;> ring

end Specialization

section Field
variable {F : Type*} [Field F]

theorem embedding_injective (h2 : (2 : F) ≠ 0) : Function.Injective (embedding F) := by
  intro v w h
  have e := congrArg (recover F) h
  rw [recover_embedding, recover_embedding] at e
  funext c
  exact mul_left_cancel₀ h2 (congrFun e c)

end Field

end Triality.Standard.OddFundamentalCentralizer.ElementaryIndex.HighestUnipotent.OrthogonalComparison
