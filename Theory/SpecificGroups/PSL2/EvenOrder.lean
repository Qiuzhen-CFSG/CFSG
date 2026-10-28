module
public import Mathlib.LinearAlgebra.Matrix.ProjectiveSpecialLinearGroup
public import Mathlib.GroupTheory.SpecificGroups.Cyclic
public import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.FinCases

/-!
# Even order of the projective special linear group of degree two

The image of the matrix with rows (0,-1) and (1,0) is a nonidentity
involution: its square is scalar, and its off-diagonal entry prevents it
from being scalar itself. Its order divides the group cardinality.
This proof also covers infinite fields, where Nat.card is zero.

Source application: the two simple-component quotients in Aschbacher--Smith,
15.2.27(2), printed p.1119. Only evenness is needed for Sylow intersection.
-/

public section
open Subgroup
open scoped MatrixGroups
namespace Theory.PSL2
variable {F : Type*} [Field F]

/-- PSL₂ over any field has even natural cardinality. -/
theorem two_dvd_card : 2 ∣ Nat.card PSL(2,F) := by
  let t : SL(2,F) := ⟨!![0,-1;1,0],by simp⟩
  let q := QuotientGroup.mk' (center SL(2,F))
  have ht : q t ≠ 1 := by
    intro he
    obtain ⟨r,_,hr⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp
      ((QuotientGroup.eq_one_iff t).mp he)
    have hh := congrArg (fun A : Matrix (Fin 2) (Fin 2) F => A 1 0) hr
    simp [t] at hh
  have ht2 : q t ^ 2 = 1 := by
    rw [←map_pow]
    apply (QuotientGroup.eq_one_iff (t^2)).mpr
    apply Matrix.SpecialLinearGroup.mem_center_iff.mpr
    refine ⟨-1,by norm_num,?_⟩
    change Matrix.scalar (Fin 2) (-1 : F) = ((t^(2:ℕ) : SL(2,F)) : Matrix (Fin 2) (Fin 2) F)
    rw [Matrix.SpecialLinearGroup.coe_pow, pow_two]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [t,Matrix.mul_apply,Fin.sum_univ_two]
  have ho : orderOf (q t) = 2 := orderOf_eq_prime ht2 ht
  simpa only [ho] using orderOf_dvd_natCard (q t)
end Theory.PSL2
