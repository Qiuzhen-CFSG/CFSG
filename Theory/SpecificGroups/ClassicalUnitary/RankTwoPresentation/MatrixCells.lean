module
public import Theory.SpecificGroups.ClassicalUnitary.RankTwoPresentation.MatrixWeyl
public import Theory.SpecificGroups.ClassicalUnitary.RankTwoPresentation.WeylWords
public import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.Tactic.FinCases

/-!
# Unitary matrix Borel diagonals and Weyl pivots

The ordered positive word followed by the full torus is upper triangular,
and its diagonal recovers the torus. Each nonidentity Weyl word has a
nonzero entry below that diagonal, in both dimensions. These calculations
are the identity-cell separation in Steinberg's Bruhat proof, Lectures on
Chevalley Groups, Theorem 4(b), pp.35–36; no group recognition is assumed.
-/
@[expose] public section
namespace Theory.SpecificGroups.ClassicalUnitary.RankTwoPresentation
open Matrix
variable {E : Type*} [Field E] (σ : E ≃+* E)
namespace Matrix4

theorem word_torus_diagonal (a d c b u v : E) (i : Fin 4) :
    (A σ a*D d*C σ c*B b*H σ u v) i i=H σ u v i i := by
  fin_cases i <;> simp [A,D,C,B,H,Matrix.mul_apply,Fin.sum_univ_succ]

theorem word_torus_triangular (a d c b u v : E) :
    (A σ a*D d*C σ c*B b*H σ u v).IsUpperTriangular := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp_all [A,D,C,B,H,Matrix.mul_apply,Fin.sum_univ_succ]

omit σ in
theorem weyl_triangular_iff (w : WeylWord) :
    (w.eval (S : Matrix (Fin 4) (Fin 4) E) T).IsUpperTriangular ↔ w=.one := by
  constructor
  · intro hw
    cases w
    · rfl
    all_goals exfalso
    · have hh := hw (by decide : (0:Fin 4)<1)
      simp [WeylWord.eval,S] at hh
    · have hh := hw (by decide : (1:Fin 4)<2)
      simp [WeylWord.eval,T] at hh
    · have hh := hw (by decide : (0:Fin 4)<1)
      simp [WeylWord.eval,S,T,Matrix.mul_apply,Fin.sum_univ_succ] at hh
    · have hh := hw (by decide : (0:Fin 4)<2)
      simp [WeylWord.eval,S,T,Matrix.mul_apply,Fin.sum_univ_succ] at hh
    · have hh := hw (by decide : (0:Fin 4)<3)
      simp [WeylWord.eval,S,T,Matrix.mul_apply,Fin.sum_univ_succ] at hh
    · have hh := hw (by decide : (0:Fin 4)<2)
      simp [WeylWord.eval,S,T,Matrix.mul_apply,Fin.sum_univ_succ] at hh
    · have hh := hw (by decide : (0:Fin 4)<3)
      simp [WeylWord.eval,S,T,Matrix.mul_apply,Fin.sum_univ_succ] at hh
  · rintro rfl
    exact Matrix.blockTriangular_one
end Matrix4
namespace Matrix5

theorem word_torus_diagonal (a y z c x v u b : E) (i : Fin 5) :
    (A σ a*D σ y z*C σ c*B σ x v*H σ u b) i i=H σ u b i i := by
  fin_cases i <;> simp [A,D,C,B,H,Matrix.mul_apply,Fin.sum_univ_succ]

theorem word_torus_triangular (a y z c x v u b : E) :
    (A σ a*D σ y z*C σ c*B σ x v*H σ u b).IsUpperTriangular := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp_all [A,D,C,B,H,Matrix.mul_apply,Fin.sum_univ_succ]

omit σ in
theorem weyl_triangular_iff (w : WeylWord) :
    (w.eval (S : Matrix (Fin 5) (Fin 5) E) T).IsUpperTriangular ↔ w=.one := by
  constructor
  · intro hw
    cases w
    · rfl
    all_goals exfalso
    · have hh := hw (by decide : (0:Fin 5)<1)
      simp [WeylWord.eval,S] at hh
    · have hh := hw (by decide : (1:Fin 5)<3)
      simp [WeylWord.eval,T] at hh
    · have hh := hw (by decide : (0:Fin 5)<1)
      simp [WeylWord.eval,S,T,Matrix.mul_apply,Fin.sum_univ_succ] at hh
    · have hh := hw (by decide : (0:Fin 5)<3)
      simp [WeylWord.eval,S,T,Matrix.mul_apply,Fin.sum_univ_succ] at hh
    · have hh := hw (by decide : (0:Fin 5)<4)
      simp [WeylWord.eval,S,T,Matrix.mul_apply,Fin.sum_univ_succ] at hh
    · have hh := hw (by decide : (0:Fin 5)<3)
      simp [WeylWord.eval,S,T,Matrix.mul_apply,Fin.sum_univ_succ] at hh
    · have hh := hw (by decide : (0:Fin 5)<4)
      simp [WeylWord.eval,S,T,Matrix.mul_apply,Fin.sum_univ_succ] at hh
  · rintro rfl
    exact Matrix.blockTriangular_one
end Matrix5
end Theory.SpecificGroups.ClassicalUnitary.RankTwoPresentation
