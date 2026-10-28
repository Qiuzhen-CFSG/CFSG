module

public import Theory.Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.ModularCertificate.SmallModels.Construction
import Mathlib.Tactic.Ring

/-!
# Spanning by translates of a rank-one matrix

If a subalgebra contains `v ⊗ λ`, and left and right translates of its factors
have matrices `P,Q` with the indicated one-sided inverses, it contains every
matrix: expand `P (Pi M Qi) Q` in these outer products. This is the algebraic
step used by the explicit degree-six and degree-fourteen ATLAS certificates.
The argument generalizes SixteenModels/Density/Spanning.lean without changing
that shared module. Its application below constructs irreducible actions of
the literal J₂ carrier. Source witness conventions: ../Source.md.
-/

public section
namespace Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.ModularCertificate.SmallModels
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

/-- The positive word convention used by all orbit and trace certificates. -/
theorem wordValue_mem (S : Subalgebra F (Matrix (Fin n) (Fin n) F))
    (A B : Matrix (Fin n) (Fin n) F) (hA : A ∈ S) (hB : B ∈ S) (w : List Bool) :
    wordValue A B w ∈ S := by
  induction w with
  | nil => exact S.one_mem
  | cons s w ih =>
    change (if s then B else A) * wordValue A B w ∈ S
    apply S.mul_mem _ ih
    cases s
    · exact hA
    · exact hB

/-- An explicit orbit certificate yields density for the two marked matrices. -/
theorem density_of_rankOne (A B : Matrix (Fin n) (Fin n) F)
    (v lam : Fin n → F) (P Pi Q Qi : Matrix (Fin n) (Fin n) F)
    (left right : Fin n → List Bool)
    (he : Matrix.vecMulVec v lam ∈
      Algebra.adjoin F ({A, B} : Set (Matrix (Fin n) (Fin n) F)))
    (hl : ∀ i, (wordValue A B (left i)).mulVec v = fun k => P k i)
    (hr : ∀ j, Matrix.vecMul lam (wordValue A B (right j)) = Q j)
    (hP : P * Pi = 1) (hQ : Qi * Q = 1) :
    Algebra.adjoin F ({A, B} : Set (Matrix (Fin n) (Fin n) F)) = ⊤ := by
  let S := Algebra.adjoin F ({A, B} : Set (Matrix (Fin n) (Fin n) F))
  have hA : A ∈ S := Algebra.subset_adjoin (by simp)
  have hB : B ∈ S := Algebra.subset_adjoin (by simp)
  exact top_of_rankOne S v lam P Pi Q Qi he
    (fun i => ⟨wordValue A B (left i), wordValue_mem S A B hA hB _, hl i⟩)
    (fun j => ⟨wordValue A B (right j), wordValue_mem S A B hA hB _, hr j⟩) hP hQ

/-- The orbit certificate supplies the irreducibility input of the literal
carrier construction. The exact presentation is the only group-theoretic input. -/
theorem action_irreducible_of_rankOne [NeZero n]
    (hp : Function.Injective
      Sporadic.LeechRelated.J2.G2FourModule.Embedding.InnerRealization.Presentation.toCarrier)
    (A B : Matrix (Fin n) (Fin n) F) (hrel : MatrixRelations A B)
    (v lam : Fin n → F) (P Pi Q Qi : Matrix (Fin n) (Fin n) F)
    (left right : Fin n → List Bool)
    (he : Matrix.vecMulVec v lam ∈
      Algebra.adjoin F ({A, B} : Set (Matrix (Fin n) (Fin n) F)))
    (hl : ∀ i, (wordValue A B (left i)).mulVec v = fun k => P k i)
    (hr : ∀ j, Matrix.vecMul lam (wordValue A B (right j)) = Q j)
    (hP : P * Pi = 1) (hQ : Qi * Q = 1) : IsIrreducible (action hp A B hrel) :=
  action_irreducible hp A B hrel (density_of_rankOne A B v lam P Pi Q Qi
    left right he hl hr hP hQ)

end Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.ModularCertificate.SmallModels
