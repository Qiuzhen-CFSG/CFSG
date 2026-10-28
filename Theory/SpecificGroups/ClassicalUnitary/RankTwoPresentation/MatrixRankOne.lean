module
public import Theory.SpecificGroups.ClassicalUnitary.RankTwoPresentation.MatrixWeyl
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring

/-!
# Literal unitary rank-one Bruhat equations

These are equations in the fixed antidiagonal coordinates. In dimension
five the two root parameters keep the condition z + conjugate(z) = norm(x).
Source: Steinberg, Lectures on Chevalley Groups, Lemma 24 and Lemma 63(c).
-/
@[expose] public section
namespace Theory.SpecificGroups.ClassicalUnitary.RankTwoPresentation
open Matrix
variable {E : Type*} [Field E] [CharP E 2] (σ : E ≃+* E)

namespace Matrix4

omit [CharP E 2] in
private theorem mul_H_S (M : Matrix (Fin 4) (Fin 4) E) (a b : E) :
    M * H σ a b * S =
      ((fun i j => M i (![1,0,3,2] j)*![a,b,(σ b)⁻¹,(σ a)⁻¹] (![1,0,3,2] j)) : Matrix (Fin 4) (Fin 4) E) := by
  apply (mul_S (M*H σ a b)).trans
  funext i j
  exact Matrix.mul_diagonal _ M i (![1,0,3,2] j)

omit [CharP E 2] in
private theorem mul_H_T (M : Matrix (Fin 4) (Fin 4) E) (a b : E) :
    M * H σ a b * T =
      ((fun i j => M i (![0,2,1,3] j)*![a,b,(σ b)⁻¹,(σ a)⁻¹] (![0,2,1,3] j)) : Matrix (Fin 4) (Fin 4) E) := by
  apply (mul_T (M*H σ a b)).trans
  funext i j
  exact Matrix.mul_diagonal _ M i (![0,2,1,3] j)

theorem S_A_bruhat (v : E) (hv : v≠0) :
    S*A σ v*S = A σ v⁻¹*H σ v⁻¹ v*S*A σ v⁻¹ := by
  have hsv : σ v≠0 := (map_ne_zero σ).mpr hv
  have hright := congrArg (fun M : Matrix (Fin 4) (Fin 4) E => M*(A σ v⁻¹))
    (mul_H_S σ (A σ v⁻¹) v⁻¹ v)
  apply Eq.trans ?_ hright.symm
  apply (S_conj (A σ v)).trans
  ext i j
  change (A σ v) (![1,0,3,2] i) (![1,0,3,2] j) =
    ∑ k, ((A σ v⁻¹) i (![1,0,3,2] k)*![v⁻¹,v,(σ (v))⁻¹,(σ (v⁻¹))⁻¹] (![1,0,3,2] k))*(A σ v⁻¹) k j
  fin_cases i <;> fin_cases j <;>
    simp [A,Fin.sum_univ_succ,hv,hsv,CharTwo.add_self_eq_zero]

theorem T_B_bruhat (v : E) (hv : v≠0) (hfix : σ v=v) :
    T*B v*T = B v⁻¹*H σ 1 v⁻¹*T*B v⁻¹ := by
  have hright := congrArg (fun M : Matrix (Fin 4) (Fin 4) E => M*(B v⁻¹))
    (mul_H_T σ (B v⁻¹) 1 v⁻¹)
  apply Eq.trans ?_ hright.symm
  apply (T_conj (B v)).trans
  ext i j
  change (B v) (![0,2,1,3] i) (![0,2,1,3] j) =
    ∑ k, ((B v⁻¹) i (![0,2,1,3] k)*![1,v⁻¹,(σ (v⁻¹))⁻¹,(σ (1))⁻¹] (![0,2,1,3] k))*(B v⁻¹) k j
  fin_cases i <;> fin_cases j <;>
    simp [B,Fin.sum_univ_succ,hv,hfix,CharTwo.add_self_eq_zero]

end Matrix4

namespace Matrix5

omit [CharP E 2] in
private theorem mul_H_S (M : Matrix (Fin 5) (Fin 5) E) (a b : E) :
    M * H σ a b * S =
      ((fun i j => M i (![1,0,2,4,3] j)*![a,b,delta σ a b,(σ b)⁻¹,(σ a)⁻¹] (![1,0,2,4,3] j)) : Matrix (Fin 5) (Fin 5) E) := by
  apply (mul_S (M*H σ a b)).trans
  funext i j
  exact Matrix.mul_diagonal _ M i (![1,0,2,4,3] j)

omit [CharP E 2] in
private theorem mul_H_T (M : Matrix (Fin 5) (Fin 5) E) (a b : E) :
    M * H σ a b * T =
      ((fun i j => M i (![0,3,2,1,4] j)*![a,b,delta σ a b,(σ b)⁻¹,(σ a)⁻¹] (![0,3,2,1,4] j)) : Matrix (Fin 5) (Fin 5) E) := by
  apply (mul_T (M*H σ a b)).trans
  funext i j
  exact Matrix.mul_diagonal _ M i (![0,3,2,1,4] j)

theorem S_A_bruhat (v : E) (hv : v≠0) :
    S*A σ v*S = A σ v⁻¹*H σ v⁻¹ v*S*A σ v⁻¹ := by
  have hsv : σ v≠0 := (map_ne_zero σ).mpr hv
  have hright := congrArg (fun M : Matrix (Fin 5) (Fin 5) E => M*(A σ v⁻¹))
    (mul_H_S σ (A σ v⁻¹) v⁻¹ v)
  apply Eq.trans ?_ hright.symm
  apply (S_conj (A σ v)).trans
  ext i j
  change (A σ v) (![1,0,2,4,3] i) (![1,0,2,4,3] j) =
    ∑ k, ((A σ v⁻¹) i (![1,0,2,4,3] k)*![v⁻¹,v,delta σ (v⁻¹) (v),(σ (v))⁻¹,(σ (v⁻¹))⁻¹] (![1,0,2,4,3] k))*(A σ v⁻¹) k j
  fin_cases i <;> fin_cases j <;>
    simp [A,delta,Fin.sum_univ_succ,hv,hsv,CharTwo.add_self_eq_zero]

theorem T_B_bruhat (hσ : Function.Involutive σ) (x z : E)
    (hz : z≠0) (hrel : z+σ z=x*σ x) :
    T*B σ x z*T =
      B σ (x/σ z) z⁻¹*H σ 1 (σ z)⁻¹*T*B σ (x/z) z⁻¹ := by
  have hsz : σ z≠0 := (map_ne_zero σ).mpr hz
  have hright := congrArg (fun M : Matrix (Fin 5) (Fin 5) E => M*(B σ (x/z) z⁻¹))
    (mul_H_T σ (B σ (x/σ z) z⁻¹) 1 (σ z)⁻¹)
  apply Eq.trans ?_ hright.symm
  apply (T_conj (B σ x z)).trans
  ext i j
  change (B σ x z) (![0,3,2,1,4] i) (![0,3,2,1,4] j) =
    ∑ k, ((B σ (x/σ z) z⁻¹) i (![0,3,2,1,4] k)*![1,(σ z)⁻¹,delta σ (1) ((σ z)⁻¹),(σ ((σ z)⁻¹))⁻¹,(σ (1))⁻¹] (![0,3,2,1,4] k))*(B σ (x/z) z⁻¹) k j
  fin_cases i <;> fin_cases j <;>
    simp [B,delta,Fin.sum_univ_succ,
      map_div₀,hσ z,hz,CharTwo.add_self_eq_zero]
  all_goals field_simp
  all_goals simp [mul_comm (σ x) x,←hrel,add_comm,add_left_comm,CharTwo.add_self_eq_zero]

end Matrix5
end Theory.SpecificGroups.ClassicalUnitary.RankTwoPresentation
