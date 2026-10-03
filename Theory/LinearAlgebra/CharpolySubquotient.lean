module

public import Mathlib.LinearAlgebra.Charpoly.ToMatrix

/-!
# Characteristic polynomials of an invariant subspace and quotient

A basis of the invariant subspace followed by lifts of a quotient basis makes
an endomorphism block triangular. Its characteristic polynomial is therefore
the product of the two diagonal characteristic polynomials.

The adapted-basis proof is adapted from Mathlib's
`LinearMap.det_eq_det_mul_det` in `Mathlib/LinearAlgebra/Determinant.lean`
(Apache 2.0; Johannes Hölzl, Patrick Massot, Casper Putz, Anne Baanen).
-/

public section

open Module.Basis

/-- The characteristic polynomial factors over an invariant subspace and its quotient. -/
theorem LinearMap.charpoly_eq_charpoly_mul_charpoly
    {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (W : Submodule K V)
    (e : V →ₗ[K] V) (he : W ≤ W.comap e) :
    e.charpoly = (e.restrict he).charpoly * (W.mapQ W e he).charpoly := by
  classical
  let m := Module.Free.ChooseBasisIndex K W
  let bW : Module.Basis m K W := Module.Free.chooseBasis K W
  let n := Module.Free.ChooseBasisIndex K (V ⧸ W)
  let bQ : Module.Basis n K (V ⧸ W) := Module.Free.chooseBasis K (V ⧸ W)
  let b := sumQuot bW bQ
  let A : Matrix m m K := LinearMap.toMatrix bW bW (e.restrict he)
  let B : Matrix m n K := Matrix.of fun i l ↦
    ((sumQuot bW bQ).repr (e ((sumQuot bW bQ) (Sum.inr l)))) (Sum.inl i)
  let D : Matrix n n K := LinearMap.toMatrix bQ bQ (W.mapQ W e he)
  suffices LinearMap.toMatrix b b e = Matrix.fromBlocks A B 0 D by
    rw [← LinearMap.charpoly_toMatrix e b, this,
      Matrix.charpoly_fromBlocks_zero₂₁]
    simp only [A, D, LinearMap.charpoly_toMatrix]
  ext u v
  cases u with
  | inl i =>
    cases v with
    | inl k =>
      simp only [b, sumQuot_inl, Matrix.fromBlocks_apply₁₁, A, LinearMap.toMatrix_apply]
      apply sumQuot_repr_inl_of_mem
    | inr l => simp [b, LinearMap.toMatrix_apply, Matrix.fromBlocks_apply₁₂, B]
  | inr j =>
    cases v with
    | inl k =>
      suffices W.mkQ (e (bW k)) = 0 by simp [LinearMap.toMatrix_apply, b, this]
      rw [← LinearMap.mem_ker, Submodule.ker_mkQ]
      exact he (Submodule.coe_mem (bW k))
    | inr l =>
      simp only [LinearMap.toMatrix_apply, sumQuot_repr_inr,
        Matrix.fromBlocks_apply₂₂, b, D]
      rw [← sumQuot_inr bW bQ l, W.mapQ_apply]
      simp
