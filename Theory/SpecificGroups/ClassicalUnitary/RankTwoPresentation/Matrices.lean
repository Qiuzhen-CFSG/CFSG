module
public import Mathlib.LinearAlgebra.Matrix.Notation
public import Mathlib.Algebra.CharP.Two
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination

/-!
# Positive unitary root matrices in antidiagonal coordinates

Both relative rank-two unitary families use the positive order A,D,C,B.
In dimension five the two multipliable roots retain their full Hermitian
parameters, with trace(z)=norm(x). These literal matrix equations supply
positive collection in the new Bruhat presentation; they are not an
abstract presentation theorem.

Source: Steinberg, Lectures on Chevalley Groups, Theorem 33 and Lemmas 63–64,
printed pp.181–187. Matrices fix the conjugation and parameter conventions.
-/

@[expose] public section
namespace Theory.SpecificGroups.ClassicalUnitary.RankTwoPresentation
open Matrix
variable {E : Type*} [Field E] [CharP E 2] (σ : E ≃+* E)

namespace Matrix4

def A (a : E) : Matrix (Fin 4) (Fin 4) E :=
  !![1,a,0,0;0,1,0,0;0,0,1,σ a;0,0,0,1]

def C (c : E) : Matrix (Fin 4) (Fin 4) E :=
  !![1,0,c,0;0,1,0,σ c;0,0,1,0;0,0,0,1]

omit [CharP E 2] σ in
def B (t : E) : Matrix (Fin 4) (Fin 4) E :=
  !![1,0,0,0;0,1,t,0;0,0,1,0;0,0,0,1]

omit [CharP E 2] σ in
def D (u : E) : Matrix (Fin 4) (Fin 4) E :=
  !![1,0,0,u;0,1,0,0;0,0,1,0;0,0,0,1]

end Matrix4

namespace Matrix5

def A (a : E) : Matrix (Fin 5) (Fin 5) E :=
  !![1,a,0,0,0;0,1,0,0,0;0,0,1,0,0;0,0,0,1,σ a;0,0,0,0,1]

def C (c : E) : Matrix (Fin 5) (Fin 5) E :=
  !![1,0,0,c,0;0,1,0,0,σ c;0,0,1,0,0;0,0,0,1,0;0,0,0,0,1]

def B (x z : E) : Matrix (Fin 5) (Fin 5) E :=
  !![1,0,0,0,0;0,1,x,z,0;0,0,1,σ x,0;0,0,0,1,0;0,0,0,0,1]

def D (y w : E) : Matrix (Fin 5) (Fin 5) E :=
  !![1,0,y,0,w;0,1,0,0,0;0,0,1,0,σ y;0,0,0,1,0;0,0,0,0,1]

omit [CharP E 2] in
/-- The full Hermitian plane radical, in the presentation's D,C,B order. -/
theorem D_C_B (y w c x z : E) : D σ y w * C σ c * B σ x z =
    !![1,0,y,y*σ x+c,w;0,1,x,z,σ c;0,0,1,σ x,σ y;0,0,0,1,0;0,0,0,0,1] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [D,C,B,Matrix.mul_apply,Fin.sum_univ_succ]

end Matrix5

namespace Matrix4

omit [CharP E 2] in
theorem A_mul (a b : E) : A σ a * A σ b = A σ (a+b) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [A,Matrix.mul_apply,Fin.sum_univ_succ,map_add,add_comm]

omit [CharP E 2] in
theorem C_mul (a b : E) : C σ a * C σ b = C σ (a+b) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [C,Matrix.mul_apply,Fin.sum_univ_succ,map_add,add_comm]

omit σ in
omit [CharP E 2] in
theorem B_mul (a b : E) : B a * B b = B (a+b) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [B,Matrix.mul_apply,Fin.sum_univ_succ,add_comm]

omit σ in
omit [CharP E 2] in
theorem D_mul (a b : E) : D a * D b = D (a+b) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [D,Matrix.mul_apply,Fin.sum_univ_succ,add_comm]

omit [CharP E 2] in
theorem A_D (a d : E) : A σ a * D d = D d * A σ a := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [A,D,Matrix.mul_apply,Fin.sum_univ_succ]

omit [CharP E 2] in
theorem C_D (c d : E) : C σ c * D d = D d * C σ c := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [C,D,Matrix.mul_apply,Fin.sum_univ_succ]

omit σ [CharP E 2] in
theorem B_D (b d : E) : B b * D d = D d * B b := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [B,D,Matrix.mul_apply,Fin.sum_univ_succ]

omit [CharP E 2] in
theorem B_C (b c : E) : B b * C σ c = C σ c * B b := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [B,C,Matrix.mul_apply,Fin.sum_univ_succ]

theorem C_A (a c : E) :
    C σ c * A σ a = A σ a * D (a*σ c+σ a*c) * C σ c := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [A,C,D,Matrix.mul_apply,Fin.sum_univ_succ]
  rw [←add_assoc,CharTwo.add_self_eq_zero,zero_add,mul_comm]

theorem B_A (a t : E) (ht : σ t=t) :
    B t * A σ a = A σ a * D (a*σ a*t) * C σ (a*t) * B t := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [A,B,C,D,Matrix.mul_apply,Fin.sum_univ_succ,map_mul,ht,
      CharTwo.add_self_eq_zero,mul_comm]
  ring_nf
  simp [CharTwo.two_eq_zero]

omit [CharP E 2] in
/-- Matrix entries recover all four ordered parameters. -/
theorem word_injective : Function.Injective (fun p : E × E × E × E =>
    A σ p.1 * D p.2.1 * C σ p.2.2.1 * B p.2.2.2) := by
  rintro ⟨a,d,c,b⟩ ⟨a',d',c',b'⟩ he
  have ha := congrArg (fun M : Matrix (Fin 4) (Fin 4) E => M 0 1) he
  have hb := congrArg (fun M : Matrix (Fin 4) (Fin 4) E => M 1 2) he
  have hc := congrArg (fun M : Matrix (Fin 4) (Fin 4) E => M 0 2) he
  have hd := congrArg (fun M : Matrix (Fin 4) (Fin 4) E => M 0 3) he
  simp [A,B,C,D,Matrix.mul_apply,Fin.sum_univ_succ] at ha hb hc hd
  subst a'; subst b'
  have hc' : c=c' := add_left_cancel hc
  subst c'
  have hd' : d=d' := add_left_cancel hd
  subst d'
  rfl

end Matrix4

namespace Matrix5

omit [CharP E 2] in
theorem A_mul (a b : E) : A σ a * A σ b = A σ (a+b) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [A,Matrix.mul_apply,Fin.sum_univ_succ,map_add,add_comm]

omit [CharP E 2] in
theorem C_mul (a b : E) : C σ a * C σ b = C σ (a+b) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [C,Matrix.mul_apply,Fin.sum_univ_succ,map_add,add_comm]

omit [CharP E 2] in
theorem B_mul (x z x' z' : E) :
    B σ x z * B σ x' z' = B σ (x+x') (z+z'+x*σ x') := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [B,Matrix.mul_apply,Fin.sum_univ_succ,map_add,add_comm]
  ring

omit [CharP E 2] in
theorem D_mul (x z x' z' : E) :
    D σ x z * D σ x' z' = D σ (x+x') (z+z'+x*σ x') := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [D,Matrix.mul_apply,Fin.sum_univ_succ,map_add,add_comm]
  ring

omit [CharP E 2] in
theorem A_D (a y w : E) : A σ a * D σ y w = D σ y w * A σ a := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [A,D,Matrix.mul_apply,Fin.sum_univ_succ]

omit [CharP E 2] in
theorem C_D (c y w : E) : C σ c * D σ y w = D σ y w * C σ c := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [C,D,Matrix.mul_apply,Fin.sum_univ_succ]

omit [CharP E 2] in
theorem B_C (x z c : E) : B σ x z * C σ c = C σ c * B σ x z := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [B,C,Matrix.mul_apply,Fin.sum_univ_succ]

theorem C_A (a c : E) :
    C σ c * A σ a = A σ a * D σ 0 (a*σ c+σ a*c) * C σ c := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [A,C,D,Matrix.mul_apply,Fin.sum_univ_succ]
  rw [←add_assoc,CharTwo.add_self_eq_zero,zero_add,mul_comm]

theorem B_D (hσ : Function.Involutive σ) (x z y w : E) :
    B σ x z * D σ y w = D σ y w * C σ (y*σ x) * B σ x z := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [B,C,D,Matrix.mul_apply,Fin.sum_univ_succ,map_mul,hσ x,CharTwo.add_self_eq_zero,mul_comm]

theorem B_A (hσ : Function.Involutive σ) (a x z : E) (hz : z+σ z=x*σ x) :
    B σ x z * A σ a =
      A σ a * D σ (a*x) (a*σ a*z) * C σ (a*σ z) * B σ x z := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [A,B,C,D,Matrix.mul_apply,Fin.sum_univ_succ,map_mul,hσ z,
      mul_assoc,CharTwo.add_self_eq_zero]
  all_goals ring_nf
  linear_combination (norm := (ring_nf; simp [CharTwo.two_eq_zero])) a*hz

omit [CharP E 2] in
/-- Ordered positive coordinates are unique, before imposing the two
Hermitian trace constraints. -/
theorem word_injective : Function.Injective (fun p : E × (E × E) × E × (E × E) =>
    A σ p.1 * D σ p.2.1.1 p.2.1.2 * C σ p.2.2.1 * B σ p.2.2.2.1 p.2.2.2.2) := by
  rintro ⟨a,⟨y,w⟩,c,⟨x,z⟩⟩ ⟨a',⟨y',w'⟩,c',⟨x',z'⟩⟩ he
  have ha := congrArg (fun M : Matrix (Fin 5) (Fin 5) E => M 0 1) he
  have hx := congrArg (fun M : Matrix (Fin 5) (Fin 5) E => M 1 2) he
  have hz := congrArg (fun M : Matrix (Fin 5) (Fin 5) E => M 1 3) he
  have hy := congrArg (fun M : Matrix (Fin 5) (Fin 5) E => M 0 2) he
  have hc := congrArg (fun M : Matrix (Fin 5) (Fin 5) E => M 0 3) he
  have hw := congrArg (fun M : Matrix (Fin 5) (Fin 5) E => M 0 4) he
  simp [A,B,C,D,Matrix.mul_apply,Fin.sum_univ_succ] at ha hx hz hy hc hw
  subst a'; subst x'; subst z'
  have hy' : y=y' := add_left_cancel hy
  subst y'
  have hc' : c=c' := add_left_cancel (add_left_cancel hc)
  subst c'
  have hw' : w=w' := add_left_cancel hw
  subst w'
  rfl

end Matrix5
end Theory.SpecificGroups.ClassicalUnitary.RankTwoPresentation
