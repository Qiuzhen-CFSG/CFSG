module

public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.Algebra.Algebra.Subalgebra.Lattice
import Mathlib.Tactic.Ring

/-!
# Spanning by translates of a rank-one matrix

If a subalgebra contains `v ⊗ λ`, and left and right translates of its factors
have matrices `P,Q` with the indicated one-sided inverses, it contains every
matrix: expand `P (Pi M Qi) Q` in these outer products. This is the algebraic
step used by the ATLAS Hall--Janko certificates in dimensions 36, 64, 84
and 160. This dimension-independent version follows the proved degree-sixteen
argument in `PSL3Three.AbsoluteDegrees.SixteenModels.Density.Spanning`.
The hypotheses are concrete matrix identities, not irreducibility assumptions.
-/

public section
namespace Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.ModularCertificate.LargeModels
open Matrix
variable {F : Type*} [Field F] {n : ℕ}

theorem product_expand (P D Q : Matrix (Fin n) (Fin n) F) :
    (∑ i, ∑ j, D i j • Matrix.vecMulVec (fun k => P k i) (Q j)) = P * D * Q := by
  ext a b
  simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, Matrix.vecMulVec,
    Matrix.mul_apply, Matrix.of_apply, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem top_of_rankOne (S : Subalgebra F (Matrix (Fin n) (Fin n) F))
    (v lam : Fin n → F) (P Pi Q Qi : Matrix (Fin n) (Fin n) F)
    (he : Matrix.vecMulVec v lam ∈ S)
    (hl : ∀ i, ∃ W ∈ S, W.mulVec v = fun k => P k i)
    (hr : ∀ j, ∃ W ∈ S, Matrix.vecMul lam W = Q j)
    (hP : P * Pi = 1) (hQ : Qi * Q = 1) : S = ⊤ := by
  have hout (i j : Fin n) : Matrix.vecMulVec (fun k => P k i) (Q j) ∈ S := by
    obtain ⟨L, hL, hl⟩ := hl i
    obtain ⟨R, hR, hr⟩ := hr j
    have h := S.mul_mem (S.mul_mem hL he) hR
    rwa [Matrix.mul_vecMulVec, Matrix.vecMulVec_mul, hl, hr] at h
  apply top_unique
  intro M _
  have hsum : (∑ i, ∑ j, (Pi * M * Qi) i j •
      Matrix.vecMulVec (fun k => P k i) (Q j)) = M := by
    rw [product_expand]
    calc
      P * (Pi * M * Qi) * Q = (P * Pi) * M * (Qi * Q) := by simp only [Matrix.mul_assoc]
      _ = M := by rw [hP, hQ, one_mul, mul_one]
  rw [← hsum]
  exact S.sum_mem fun i _ => S.sum_mem fun j _ => S.smul_mem (hout i j) _
end Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.ModularCertificate.LargeModels
