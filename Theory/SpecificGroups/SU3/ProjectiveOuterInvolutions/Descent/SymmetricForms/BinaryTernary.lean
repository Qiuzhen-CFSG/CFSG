module

public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.Algebra.CharP.Reduced
public import Mathlib.Algebra.CharP.Two
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Symmetric ternary forms over a finite binary field

A nondegenerate symmetric matrix of odd order three cannot have zero diagonal
in characteristic two. Splitting off a nonzero diagonal entry leaves a
nondegenerate symmetric binary block. An alternating block is hyperbolic;
otherwise another diagonal pivot makes the entire form diagonal. Every element
of the finite binary field is a square, so both cases give the antidiagonal
Gram matrix with all three antidiagonal entries equal to one.

The proof uses explicit congruences and obtains invertibility from the final
Gram identity. It includes the field with two elements.

This is the ternary linear algebra used in GLS, Volume 3, §2.7 and the proof of
Proposition 4.9.2(b2,g), and in Volume 4, Chapter 4, Lemma 3.4(a,c).
-/

open Matrix
namespace Matrix.SymmetricTernary
variable {F : Type*} [Field F]

private def Normalizable (S : Matrix (Fin 3) (Fin 3) F) : Prop :=
  ∃ C : Matrix (Fin 3) (Fin 3) F,
    C.transpose * S * C = !![0,0,1;0,1,0;1,0,0]

private lemma transport {S T : Matrix (Fin 3) (Fin 3) F}
    (P : Matrix (Fin 3) (Fin 3) F) (hP : P.transpose * S * P = T)
    (hT : Normalizable T) : Normalizable S := by
  obtain ⟨C, hC⟩ := hT
  refine ⟨P * C, ?_⟩
  rw [transpose_mul]
  calc
    C.transpose * P.transpose * S * (P * C) =
      C.transpose * (P.transpose * S * P) * C := by simp only [mul_assoc]
    _ = _ := by rw [hP, hC]

private lemma det_congr_ne_zero {S T : Matrix (Fin 3) (Fin 3) F}
    (P : Matrix (Fin 3) (Fin 3) F) (hP : P.transpose * S * P = T)
    (hp : P.det ≠ 0) (hs : S.det ≠ 0) : T.det ≠ 0 := by
  rw [← hP, det_mul, det_mul, det_transpose]
  exact mul_ne_zero (mul_ne_zero hp hs) hp

-- Split off a nonisotropic coordinate by simultaneous row and column operations.
private lemma eliminate (a b c d e f : F) (ha : a ≠ 0) :
    let P : Matrix (Fin 3) (Fin 3) F := !![1, -b/a, -c/a; 0,1,0; 0,0,1]
    P.transpose * !![a,b,c;b,d,e;c,e,f] * P =
      !![a,0,0;0,d-b^2/a,e-b*c/a;0,e-b*c/a,f-c^2/a] := by
  dsimp
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_succ] <;> field_simp <;> ring

variable [CharP F 2]

-- Squaring is surjective in the finite binary field. After scaling the three
-- orthogonal vectors to norm one, their pairwise sums give a hyperbolic pair.
private lemma diagonal [Finite F] (a d f : F) (ha : a ≠ 0) (hd : d ≠ 0)
    (hf : f ≠ 0) : Normalizable (!![a,0,0;0,d,0;0,0,f] : Matrix (Fin 3) (Fin 3) F) := by
  obtain ⟨r, rfl⟩ := isSquare_of_charTwo' a
  obtain ⟨s, rfl⟩ := isSquare_of_charTwo' d
  obtain ⟨t, rfl⟩ := isSquare_of_charTwo' f
  have hr : r ≠ 0 := left_ne_zero_of_mul ha
  have hs : s ≠ 0 := left_ne_zero_of_mul hd
  have ht : t ≠ 0 := left_ne_zero_of_mul hf
  refine ⟨!![r⁻¹,r⁻¹,0;s⁻¹,s⁻¹,s⁻¹;0,t⁻¹,t⁻¹], ?_⟩
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_succ, hr, hs, ht,
      CharTwo.add_self_eq_zero]

private lemma hyperbolic [Finite F] (a e : F) (ha : a ≠ 0) (he : e ≠ 0) :
    Normalizable (!![a,0,0;0,0,e;0,e,0] : Matrix (Fin 3) (Fin 3) F) := by
  obtain ⟨r, rfl⟩ := isSquare_of_charTwo' a
  have hr : r ≠ 0 := left_ne_zero_of_mul ha
  refine ⟨!![0,r⁻¹,0;1,0,0;0,0,e⁻¹], ?_⟩
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_succ, hr, he, mul_assoc]

private lemma block_pivot [Finite F] (a d e f : F) (ha : a ≠ 0) (hd : d ≠ 0)
    (hdet : (!![a,0,0;0,d,e;0,e,f] : Matrix (Fin 3) (Fin 3) F).det ≠ 0) :
    Normalizable (!![a,0,0;0,d,e;0,e,f] : Matrix (Fin 3) (Fin 3) F) := by
  let P : Matrix (Fin 3) (Fin 3) F := !![1,0,0;0,1,-e/d;0,0,1]
  have hP : P.transpose * !![a,0,0;0,d,e;0,e,f] * P =
      !![a,0,0;0,d,0;0,0,f-e^2/d] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [P, Matrix.mul_apply, Fin.sum_univ_succ] <;> field_simp <;> ring
  have hp : P.det ≠ 0 := by simp [P, Matrix.det_fin_three]
  have hf : f - e^2/d ≠ 0 := by
    have h := det_congr_ne_zero P hP hp hdet
    simpa [Matrix.det_fin_three, ha, hd] using h
  exact transport P hP (diagonal a d _ ha hd hf)

-- A nondegenerate binary block is either alternating, or has a diagonal pivot.
private lemma block [Finite F] (a d e f : F) (ha : a ≠ 0)
    (hdet : (!![a,0,0;0,d,e;0,e,f] : Matrix (Fin 3) (Fin 3) F).det ≠ 0) :
    Normalizable (!![a,0,0;0,d,e;0,e,f] : Matrix (Fin 3) (Fin 3) F) := by
  by_cases hd : d = 0
  · subst d
    by_cases hf : f = 0
    · subst f
      have he : e ≠ 0 := by
        intro he
        apply hdet
        simp [he, Matrix.det_fin_three]
      exact hyperbolic a e ha he
    · let P : Matrix (Fin 3) (Fin 3) F := !![1,0,0;0,0,1;0,1,0]
      have hP : P.transpose * !![a,0,0;0,0,e;0,e,f] * P =
          !![a,0,0;0,f,e;0,e,0] := by
        ext i j
        fin_cases i <;> fin_cases j <;> simp [P, Matrix.mul_apply, Fin.sum_univ_succ]
      have hp : P.det ≠ 0 := by simp [P, Matrix.det_fin_three]
      exact transport P hP (block_pivot a f e 0 ha hf (det_congr_ne_zero P hP hp hdet))
  · exact block_pivot a d e f ha hd hdet

private lemma pivot [Finite F] (a b c d e f : F) (ha : a ≠ 0)
    (hdet : (!![a,b,c;b,d,e;c,e,f] : Matrix (Fin 3) (Fin 3) F).det ≠ 0) :
    Normalizable (!![a,b,c;b,d,e;c,e,f] : Matrix (Fin 3) (Fin 3) F) := by
  let P : Matrix (Fin 3) (Fin 3) F := !![1,-b/a,-c/a;0,1,0;0,0,1]
  have hP := eliminate a b c d e f ha
  have hp : P.det ≠ 0 := by simp [P, Matrix.det_fin_three]
  exact transport P hP (block a _ _ _ ha (det_congr_ne_zero P hP hp hdet))

-- The all-zero diagonal case has determinant zero in dimension three.
private lemma entries [Finite F] (a b c d e f : F)
    (hdet : (!![a,b,c;b,d,e;c,e,f] : Matrix (Fin 3) (Fin 3) F).det ≠ 0) :
    Normalizable (!![a,b,c;b,d,e;c,e,f] : Matrix (Fin 3) (Fin 3) F) := by
  by_cases ha : a = 0
  · subst a
    by_cases hd : d = 0
    · subst d
      by_cases hf : f = 0
      · subst f
        exfalso
        apply hdet
        simp [Matrix.det_fin_three]
        ring_nf
        simp [CharTwo.two_eq_zero]
      · let P : Matrix (Fin 3) (Fin 3) F := !![0,0,1;0,1,0;1,0,0]
        have hP : P.transpose * !![0,b,c;b,0,e;c,e,f] * P =
            !![f,e,c;e,0,b;c,b,0] := by
          ext i j
          fin_cases i <;> fin_cases j <;> simp [P, Matrix.mul_apply, Fin.sum_univ_succ]
        have hp : P.det ≠ 0 := by simp [P, Matrix.det_fin_three]
        exact transport P hP (pivot f e c 0 b 0 hf (det_congr_ne_zero P hP hp hdet))
    · let P : Matrix (Fin 3) (Fin 3) F := !![0,1,0;1,0,0;0,0,1]
      have hP : P.transpose * !![0,b,c;b,d,e;c,e,f] * P =
          !![d,b,e;b,0,c;e,c,f] := by
        ext i j
        fin_cases i <;> fin_cases j <;> simp [P, Matrix.mul_apply, Fin.sum_univ_succ]
      have hp : P.det ≠ 0 := by simp [P, Matrix.det_fin_three]
      exact transport P hP (pivot d b e 0 c f hd (det_congr_ne_zero P hP hp hdet))
  · exact pivot a b c d e f ha hdet

/-- Every nondegenerate symmetric ternary form over a finite field of
characteristic two admits a basis with the antidiagonal Gram matrix. -/
public theorem exists_congruence_antidiagonal [Finite F] (S : Matrix (Fin 3) (Fin 3) F)
    (hs : S.transpose = S) (hd : S.det ≠ 0) :
    ∃ C : GL (Fin 3) F, C.val.transpose * S * C.val = !![0,0,1;0,1,0;1,0,0] := by
  have h10 : S 1 0 = S 0 1 := congrArg (fun M : Matrix (Fin 3) (Fin 3) F => M 0 1) hs
  have h20 : S 2 0 = S 0 2 := congrArg (fun M : Matrix (Fin 3) (Fin 3) F => M 0 2) hs
  have h21 : S 2 1 = S 1 2 := congrArg (fun M : Matrix (Fin 3) (Fin 3) F => M 1 2) hs
  have hS : S = !![S 0 0,S 0 1,S 0 2;S 0 1,S 1 1,S 1 2;S 0 2,S 1 2,S 2 2] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [h10, h20, h21]
  obtain ⟨C, hC⟩ : Normalizable S := by
    rw [hS] at hd ⊢
    exact entries _ _ _ _ _ _ hd
  have hc : C.det ≠ 0 := by
    intro hc
    have h := congrArg Matrix.det hC
    simp [Matrix.det_mul, Matrix.det_transpose, hc, Matrix.det_fin_three] at h
  exact ⟨GeneralLinearGroup.mkOfDetNeZero C hc, hC⟩

end Matrix.SymmetricTernary
