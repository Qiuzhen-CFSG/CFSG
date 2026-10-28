module

public import Mathlib.Algebra.Algebra.Subalgebra.Lattice
public import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Data.Fin.Basic

/-!
# Finite orbit trees and spanning rows

A parent array with parent(i) ≤ i certifies a finite tree of algebra translates.
Column actions multiply on the left; row actions multiply on the right.
A left inverse of the matrix storing these vectors as rows makes them span
any submodule that contains them. The HS specialization in `OrbitSpans.lean`
uses the literal normalized null vectors and the two published orbit trees.

Source: `Certificates/source/README.md`, structural density certificate and
zero-based orbit conventions. These arguments use no finite rank assumptions.
-/

public section
namespace Representation.HigmanSims.LargeModels.TracePair.Certificates.OrbitSpans

variable {K ι : Type*} [Field K] [Fintype ι] [DecidableEq ι]

/-- A left inverse of the row matrix puts every vector in any subspace containing its rows. -/
theorem eq_top_of_left_inverse (W : Submodule K (ι → K))
    (C D : Matrix ι ι K) (hDC : D * C = 1) (hC : ∀ i, C i ∈ W) : W = ⊤ := by
  apply top_unique
  intro x _
  have hx : Matrix.vecMul (Matrix.vecMul x D) C ∈ W := by
    rw [Matrix.vecMul_eq_sum]
    exact W.sum_mem fun i _ => W.smul_mem _ (hC i)
  simpa only [Matrix.vecMul_vecMul, hDC, Matrix.vecMul_one] using hx

/-- Parent indices strictly decrease, so every saved column is an actual algebra translate. -/
theorem column_translates {n : ℕ} (S : Subalgebra K (Matrix ι ι K))
    (a : Fin n → Matrix ι ι K) (ha : ∀ i, a i ∈ S)
    (v : ι → K) (C : Fin (n + 1) → ι → K)
    (p : Fin n → Fin (n + 1)) (hp : ∀ i, (p i).val ≤ i.val)
    (h0 : C 0 = v) (hs : ∀ i, C i.succ = (a i).mulVec (C (p i))) :
    ∀ i, ∃ M ∈ S, M.mulVec v = C i := by
  apply Fin.strong_induction_on
  intro j ih
  revert ih
  refine Fin.cases ?_ (fun i ih => ?_) j
  · intro _
    exact ⟨1, S.one_mem, by rw [h0, Matrix.one_mulVec]⟩
  · obtain ⟨M, hM, hMv⟩ := ih (p i) (by exact Nat.lt_succ_of_le (hp i))
    refine ⟨a i * M, S.mul_mem (ha i) hM, ?_⟩
    rw [← Matrix.mulVec_mulVec, hMv, hs]

/-- The row convention composes each new generator on the right. -/
theorem row_translates {n : ℕ} (S : Subalgebra K (Matrix ι ι K))
    (a : Fin n → Matrix ι ι K) (ha : ∀ i, a i ∈ S)
    (v : ι → K) (C : Fin (n + 1) → ι → K)
    (p : Fin n → Fin (n + 1)) (hp : ∀ i, (p i).val ≤ i.val)
    (h0 : C 0 = v) (hs : ∀ i, C i.succ = Matrix.vecMul (C (p i)) (a i)) :
    ∀ i, ∃ M ∈ S, Matrix.vecMul v M = C i := by
  apply Fin.strong_induction_on
  intro j ih
  revert ih
  refine Fin.cases ?_ (fun i ih => ?_) j
  · intro _
    exact ⟨1, S.one_mem, by rw [h0, Matrix.vecMul_one]⟩
  · obtain ⟨M, hM, hMv⟩ := ih (p i) (by exact Nat.lt_succ_of_le (hp i))
    refine ⟨M * a i, S.mul_mem hM (ha i), ?_⟩
    rw [← Matrix.vecMul_vecMul, hMv, hs]

end Representation.HigmanSims.LargeModels.TracePair.Certificates.OrbitSpans
