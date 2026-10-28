module
public import Theory.SpecificGroups.ClassicalUnitary.RankTwoPresentation.Matrices
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring

/-!
# Diagonal and Weyl matrices for the two unitary rank-two presentations

The matrices use the antidiagonal coordinates of `Matrices`. The full
five-dimensional torus includes its determinant-correcting middle entry.
These equations are concrete inputs to the abstract Bruhat argument.
Source: Steinberg, Lectures on Chevalley Groups, Lemmas 24–26 and 63–64.
-/
@[expose] public section
namespace Theory.SpecificGroups.ClassicalUnitary.RankTwoPresentation
open Matrix
variable {E : Type*} [Field E] (σ : E ≃+* E)

private theorem fourth_power_eq_one {M : Type*} [Monoid M] (g r : M)
    (hg : g^2=r) (hr : r^2=1) : g^4=1 := by
  calc
    g^4=(g^2)^2 := pow_mul g 2 2
    _ = 1 := by rw [hg,hr]

namespace Matrix4

def H (a b : E) : Matrix (Fin 4) (Fin 4) E :=
  Matrix.diagonal ![a,b,(σ b)⁻¹,(σ a)⁻¹]

def S : Matrix (Fin 4) (Fin 4) E :=
  !![0,1,0,0;1,0,0,0;0,0,0,1;0,0,1,0]

def T : Matrix (Fin 4) (Fin 4) E :=
  !![1,0,0,0;0,0,1,0;0,1,0,0;0,0,0,1]

theorem S_mul (M : Matrix (Fin 4) (Fin 4) E) :
    S * M = ((fun i j => M (![1,0,3,2] i) j) : Matrix (Fin 4) (Fin 4) E) := by
  ext i j
  change (∑ k, S i k * M k j) = M (![1,0,3,2] i) j
  fin_cases i <;> simp [S,Fin.sum_univ_succ]

theorem mul_S (M : Matrix (Fin 4) (Fin 4) E) :
    M * S = ((fun i j => M i (![1,0,3,2] j)) : Matrix (Fin 4) (Fin 4) E) := by
  ext i j
  change (∑ k, M i k * S k j) = M i (![1,0,3,2] j)
  fin_cases j <;> simp [S,Fin.sum_univ_succ]

theorem T_mul (M : Matrix (Fin 4) (Fin 4) E) :
    T * M = ((fun i j => M (![0,2,1,3] i) j) : Matrix (Fin 4) (Fin 4) E) := by
  ext i j
  change (∑ k, T i k * M k j) = M (![0,2,1,3] i) j
  fin_cases i <;> simp [T,Fin.sum_univ_succ]

theorem mul_T (M : Matrix (Fin 4) (Fin 4) E) :
    M * T = ((fun i j => M i (![0,2,1,3] j)) : Matrix (Fin 4) (Fin 4) E) := by
  ext i j
  change (∑ k, M i k * T k j) = M i (![0,2,1,3] j)
  fin_cases j <;> simp [T,Fin.sum_univ_succ]

theorem S_conj (M : Matrix (Fin 4) (Fin 4) E) :
    S*M*S=((fun i j => M (![1,0,3,2] i) (![1,0,3,2] j)) : Matrix (Fin 4) (Fin 4) E) := by
  apply (mul_S (S*M)).trans
  funext i j
  exact congrFun (congrFun (S_mul M) i) (![1,0,3,2] j)

theorem T_conj (M : Matrix (Fin 4) (Fin 4) E) :
    T*M*T=((fun i j => M (![0,2,1,3] i) (![0,2,1,3] j)) : Matrix (Fin 4) (Fin 4) E) := by
  apply (mul_T (T*M)).trans
  funext i j
  exact congrFun (congrFun (T_mul M) i) (![0,2,1,3] j)

variable (E) in
theorem S_sq : (S : Matrix (Fin 4) (Fin 4) E)^2=1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [S,pow_two,Matrix.mul_apply,Fin.sum_univ_succ]

variable (E) in
theorem T_sq : (T : Matrix (Fin 4) (Fin 4) E)^2=1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [T,pow_two,Matrix.mul_apply,Fin.sum_univ_succ]

variable (E) in
theorem ST_sq : ((S : Matrix (Fin 4) (Fin 4) E)*T)^2=!![0,0,0,1;0,0,1,0;0,1,0,0;1,0,0,0] := by
  have hc : (S : Matrix (Fin 4) (Fin 4) E)*T*S*T =
      ((fun i j => T (![1,0,3,2] i) (![1,0,3,2] (![0,2,1,3] j))) : Matrix (Fin 4) (Fin 4) E) := by
    apply (mul_T (S*T*S)).trans
    funext i j
    exact congrFun (congrFun (S_conj T) i) (![0,2,1,3] j)
  apply (pow_two (M := Matrix (Fin 4) (Fin 4) E) (S*T)).trans
  apply (Matrix.mul_assoc (S*T) S T).symm.trans
  apply hc.trans
  ext i j
  fin_cases i <;> fin_cases j <;> simp [T]

variable (E) in
theorem ST_four : ((S : Matrix (Fin 4) (Fin 4) E)*T)^4=1 := by
  have hr : (!![0,0,0,1;0,0,1,0;0,1,0,0;1,0,0,0] : Matrix (Fin 4) (Fin 4) E)^2=1 := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [pow_two,Matrix.mul_apply,Fin.sum_univ_succ]
  exact fourth_power_eq_one (M := Matrix (Fin 4) (Fin 4) E) (S*T) _ (ST_sq E) hr

theorem S_H (a b : E) : S * H σ a b * S = H σ b a := by
  apply (S_conj (H σ a b)).trans
  ext i j
  fin_cases i <;> fin_cases j <;> simp [H]

theorem T_H (hσ : Function.Involutive σ) (a b : E) :
    T * H σ a b * T = H σ a (σ b)⁻¹ := by
  apply (T_conj (H σ a b)).trans
  ext i j
  fin_cases i <;> fin_cases j <;> simp [H,hσ b]

theorem H_mul (a b c d : E) : H σ a b * H σ c d=H σ (a*c) (b*d) := by
  simp only [H, Matrix.diagonal_mul_diagonal]
  congr 1
  ext i
  fin_cases i <;> simp [mul_comm]

theorem H_one : H σ 1 1=1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [H]

theorem H_injective : Function.Injective (fun p : E × E => H σ p.1 p.2) := by
  intro p q he
  apply Prod.ext
  · simpa [H] using congrArg (fun M : Matrix (Fin 4) (Fin 4) E => M 0 0) he
  · simpa [H] using congrArg (fun M : Matrix (Fin 4) (Fin 4) E => M 1 1) he

theorem S_B (b : E) : S * B b * S=D b := by
  apply (S_conj (B b)).trans
  ext i j
  fin_cases i <;> fin_cases j <;> simp [B,D]

theorem S_C (hσ : Function.Involutive σ) (c : E) : S * C σ c * S=C σ (σ c) := by
  apply (S_conj (C σ c)).trans
  ext i j
  fin_cases i <;> fin_cases j <;> simp [C,hσ c]

theorem T_A (a : E) : T * A σ a * T=C σ a := by
  apply (T_conj (A σ a)).trans
  ext i j
  fin_cases i <;> fin_cases j <;> simp [A,C]

theorem T_D (d : E) : T * D d * T=D d := by
  apply (T_conj (D d)).trans
  ext i j
  fin_cases i <;> fin_cases j <;> simp [D]
end Matrix4

namespace Matrix5

def delta (a b : E) : E := σ (a*b)/(a*b)

def H (a b : E) : Matrix (Fin 5) (Fin 5) E :=
  Matrix.diagonal ![a,b,delta σ a b,(σ b)⁻¹,(σ a)⁻¹]

def S : Matrix (Fin 5) (Fin 5) E :=
  !![0,1,0,0,0;1,0,0,0,0;0,0,1,0,0;0,0,0,0,1;0,0,0,1,0]

def T : Matrix (Fin 5) (Fin 5) E :=
  !![1,0,0,0,0;0,0,0,1,0;0,0,1,0,0;0,1,0,0,0;0,0,0,0,1]

theorem S_mul (M : Matrix (Fin 5) (Fin 5) E) :
    S * M = ((fun i j => M (![1,0,2,4,3] i) j) : Matrix (Fin 5) (Fin 5) E) := by
  ext i j
  change (∑ k, S i k * M k j) = M (![1,0,2,4,3] i) j
  fin_cases i <;> simp [S,Fin.sum_univ_succ]

theorem mul_S (M : Matrix (Fin 5) (Fin 5) E) :
    M * S = ((fun i j => M i (![1,0,2,4,3] j)) : Matrix (Fin 5) (Fin 5) E) := by
  ext i j
  change (∑ k, M i k * S k j) = M i (![1,0,2,4,3] j)
  fin_cases j <;> simp [S,Fin.sum_univ_succ]

theorem T_mul (M : Matrix (Fin 5) (Fin 5) E) :
    T * M = ((fun i j => M (![0,3,2,1,4] i) j) : Matrix (Fin 5) (Fin 5) E) := by
  ext i j
  change (∑ k, T i k * M k j) = M (![0,3,2,1,4] i) j
  fin_cases i <;> simp [T,Fin.sum_univ_succ]

theorem mul_T (M : Matrix (Fin 5) (Fin 5) E) :
    M * T = ((fun i j => M i (![0,3,2,1,4] j)) : Matrix (Fin 5) (Fin 5) E) := by
  ext i j
  change (∑ k, M i k * T k j) = M i (![0,3,2,1,4] j)
  fin_cases j <;> simp [T,Fin.sum_univ_succ]

theorem S_conj (M : Matrix (Fin 5) (Fin 5) E) :
    S*M*S=((fun i j => M (![1,0,2,4,3] i) (![1,0,2,4,3] j)) : Matrix (Fin 5) (Fin 5) E) := by
  apply (mul_S (S*M)).trans
  funext i j
  exact congrFun (congrFun (S_mul M) i) (![1,0,2,4,3] j)

theorem T_conj (M : Matrix (Fin 5) (Fin 5) E) :
    T*M*T=((fun i j => M (![0,3,2,1,4] i) (![0,3,2,1,4] j)) : Matrix (Fin 5) (Fin 5) E) := by
  apply (mul_T (T*M)).trans
  funext i j
  exact congrFun (congrFun (T_mul M) i) (![0,3,2,1,4] j)

variable (E) in
theorem S_sq : (S : Matrix (Fin 5) (Fin 5) E)^2=1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [S,pow_two,Matrix.mul_apply,Fin.sum_univ_succ]

variable (E) in
theorem T_sq : (T : Matrix (Fin 5) (Fin 5) E)^2=1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [T,pow_two,Matrix.mul_apply,Fin.sum_univ_succ]

variable (E) in
theorem ST_sq : ((S : Matrix (Fin 5) (Fin 5) E)*T)^2=!![0,0,0,0,1;0,0,0,1,0;0,0,1,0,0;0,1,0,0,0;1,0,0,0,0] := by
  have hc : (S : Matrix (Fin 5) (Fin 5) E)*T*S*T =
      ((fun i j => T (![1,0,2,4,3] i) (![1,0,2,4,3] (![0,3,2,1,4] j))) : Matrix (Fin 5) (Fin 5) E) := by
    apply (mul_T (S*T*S)).trans
    funext i j
    exact congrFun (congrFun (S_conj T) i) (![0,3,2,1,4] j)
  apply (pow_two (M := Matrix (Fin 5) (Fin 5) E) (S*T)).trans
  apply (Matrix.mul_assoc (S*T) S T).symm.trans
  apply hc.trans
  ext i j
  fin_cases i <;> fin_cases j <;> simp [T]

variable (E) in
theorem ST_four : ((S : Matrix (Fin 5) (Fin 5) E)*T)^4=1 := by
  have hr : (!![0,0,0,0,1;0,0,0,1,0;0,0,1,0,0;0,1,0,0,0;1,0,0,0,0] : Matrix (Fin 5) (Fin 5) E)^2=1 := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [pow_two,Matrix.mul_apply,Fin.sum_univ_succ]
  exact fourth_power_eq_one (M := Matrix (Fin 5) (Fin 5) E) (S*T) _ (ST_sq E) hr

theorem S_H (a b : E) : S * H σ a b * S = H σ b a := by
  apply (S_conj (H σ a b)).trans
  ext i j
  fin_cases i <;> fin_cases j <;> simp [H,delta,mul_comm]

theorem T_H (hσ : Function.Involutive σ) (a b : E) :
    T * H σ a b * T = H σ a (σ b)⁻¹ := by
  apply (T_conj (H σ a b)).trans
  ext i j
  fin_cases i <;> fin_cases j <;> simp [H,hσ b,delta,div_eq_mul_inv,mul_comm,mul_left_comm,mul_assoc]

theorem H_mul (a b c d : E) : H σ a b * H σ c d=H σ (a*c) (b*d) := by
  simp only [H, Matrix.diagonal_mul_diagonal]
  congr 1
  ext i
  fin_cases i <;> simp [delta,div_eq_mul_inv,mul_comm,mul_left_comm,mul_assoc]

theorem H_one : H σ 1 1=1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [H,delta]

theorem H_injective : Function.Injective (fun p : E × E => H σ p.1 p.2) := by
  intro p q he
  apply Prod.ext
  · simpa [H] using congrArg (fun M : Matrix (Fin 5) (Fin 5) E => M 0 0) he
  · simpa [H] using congrArg (fun M : Matrix (Fin 5) (Fin 5) E => M 1 1) he

theorem S_B (x z : E) : S * B σ x z * S=D σ x z := by
  apply (S_conj (B σ x z)).trans
  ext i j
  fin_cases i <;> fin_cases j <;> simp [B,D]

theorem S_C (hσ : Function.Involutive σ) (c : E) : S * C σ c * S=C σ (σ c) := by
  apply (S_conj (C σ c)).trans
  ext i j
  fin_cases i <;> fin_cases j <;> simp [C,hσ c]

theorem T_A (a : E) : T * A σ a * T=C σ a := by
  apply (T_conj (A σ a)).trans
  ext i j
  fin_cases i <;> fin_cases j <;> simp [A,C]

theorem T_D (y w : E) : T * D σ y w * T=D σ y w := by
  apply (T_conj (D σ y w)).trans
  ext i j
  fin_cases i <;> fin_cases j <;> simp [D]
end Matrix5
end Theory.SpecificGroups.ClassicalUnitary.RankTwoPresentation
