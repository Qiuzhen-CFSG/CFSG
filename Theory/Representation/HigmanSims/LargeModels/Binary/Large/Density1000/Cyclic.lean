module
public import Mathlib.LinearAlgebra.Matrix.ToLin
/-!
# Certifying a rank-one polynomial on a cyclic row

Operators commuting with D are determined by their value on the first row of
a spanning Krylov chain. Consequently, to identify a polynomial in D with the
outer product u v, it suffices to certify D u = 0, v D = 0 and the polynomial's
value on that first row. This replaces a family of full matrix products by
vector recurrences and one spanning calculation.

The intended application is the degree-1000 ATLAS HS witness documented in
`Binary/source/README.md`. `Density1000.polynomial_identity_of_cyclic_rows`
applies this argument to its literal generators and polynomial. The argument
is elementary linear algebra and uses no group-action or classification input.
-/

@[expose] public section
open Matrix
open scoped BigOperators
namespace Representation.HigmanSims.LargeModels.Binary.Large.Density1000

/-- Agreement on the first vector of a spanning Krylov chain determines any
operator commuting with the chain operator. -/
theorem eq_of_cyclic_rows
    {k n : Type*} [CommRing k] [Fintype n] [DecidableEq n] {r : ℕ}
    (D P Q : Matrix n n k) (xs : Fin (r+1) → n → k)
    (hspan : Submodule.span k (Set.range xs) = ⊤)
    (hstep : ∀ i : Fin r, vecMul (xs i.castSucc) D = xs i.succ)
    (hP : P * D = D * P) (hQ : Q * D = D * Q)
    (hfirst : vecMul (xs 0) P = vecMul (xs 0) Q) : P = Q := by
  have he (i : Fin (r+1)) : vecMul (xs i) P = vecMul (xs i) Q := by
    induction i using Fin.induction with
    | zero => exact hfirst
    | succ i ih =>
      rw [← hstep i, vecMul_vecMul, ← hP, ← vecMul_vecMul, ih,
        vecMul_vecMul, hQ, ← vecMul_vecMul]
  apply Matrix.vecMul_injective
  exact congrArg DFunLike.coe (LinearMap.ext_on_range hspan he :
    P.vecMulLinear = Q.vecMulLinear)

/-- The vectors in a checked Krylov chain are the corresponding powers applied
on the right of its initial vector. -/
theorem cyclic_row_eq_power
    {k n : Type*} [CommRing k] [Fintype n] [DecidableEq n] {r : ℕ}
    (D : Matrix n n k) (xs : Fin (r+1) → n → k)
    (hstep : ∀ i : Fin r, vecMul (xs i.castSucc) D = xs i.succ)
    (i : Fin (r+1)) : vecMul (xs 0) (D ^ i.val) = xs i := by
  induction i using Fin.induction with
  | zero => simp
  | succ i ih =>
    simpa only [Fin.val_succ, pow_succ, ← vecMul_vecMul, Fin.val_castSucc] using
      (congrArg (fun x => vecMul x D) ih).trans (hstep i)

/-- A polynomial in a matrix is rank one if it has the right value on a cyclic
row and both factors of the rank-one operator are annihilated by the matrix.
Only vector identities and a spanning certificate are required. -/
theorem polynomial_eq_rank_one_of_cyclic_rows
    {k n : Type*} [CommRing k] [Fintype n] [DecidableEq n] {r : ℕ}
    (D : Matrix n n k) (xs : Fin (r+1) → n → k) (c : Fin (r+1) → k)
    (u v : n → k)
    (hspan : Submodule.span k (Set.range xs) = ⊤)
    (hstep : ∀ i : Fin r, vecMul (xs i.castSucc) D = xs i.succ)
    (hu : D.mulVec u = 0) (hv : vecMul v D = 0)
    (himage : ∑ i, c i • xs i = vecMul (xs 0) (vecMulVec u v)) :
    (∑ i, c i • D ^ i.val) = vecMulVec u v := by
  apply eq_of_cyclic_rows D _ _ xs hspan hstep
  · simp only [Finset.sum_mul, Finset.mul_sum, smul_mul_assoc, mul_smul_comm,
      ← pow_succ, ← pow_succ']
  · rw [vecMulVec_mul, mul_vecMulVec, hu, hv, vecMulVec_zero, zero_vecMulVec]
  · rw [Matrix.vecMul_sum]
    simpa only [vecMul_smul, cyclic_row_eq_power D xs hstep] using himage

/-- The same calculation puts the rank-one operator in every subalgebra
containing the Krylov operator. -/
theorem rank_one_mem_of_cyclic_rows
    {k n : Type*} [CommRing k] [Fintype n] [DecidableEq n] {r : ℕ}
    (Q : Subalgebra k (Matrix n n k)) (D : Matrix n n k)
    (xs : Fin (r+1) → n → k) (c : Fin (r+1) → k) (u v : n → k)
    (hD : D ∈ Q) (hspan : Submodule.span k (Set.range xs) = ⊤)
    (hstep : ∀ i : Fin r, vecMul (xs i.castSucc) D = xs i.succ)
    (hu : D.mulVec u = 0) (hv : vecMul v D = 0)
    (himage : ∑ i, c i • xs i = vecMul (xs 0) (vecMulVec u v)) :
    vecMulVec u v ∈ Q := by
  rw [← polynomial_eq_rank_one_of_cyclic_rows D xs c u v hspan hstep hu hv himage]
  exact Q.sum_mem fun i _ => Q.smul_mem (Q.pow_mem hD _) _
end Representation.HigmanSims.LargeModels.Binary.Large.Density1000
