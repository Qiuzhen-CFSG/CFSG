module
public import Theory.SpecificGroups.GL2.SubgroupCenter
public import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.LinearCombination
/-!
# Abelian normal subgroups of GL₂ in odd characteristic

If a matrix commutes with all its conjugates, conjugation by the two
elementary shears forces its off-diagonal entries to vanish and its two
diagonal entries to agree. Thus every abelian normal subgroup is scalar.
The calculation includes the field of order three and makes no cyclic
claim about its quaternion two-core. It supplies the inner intersection
in the odd PSL₃ involution-centralizer application of E.2.15.
-/
public section
open Subgroup Matrix
open scoped MatrixGroups IsMulCommutative
namespace Matrix.GeneralLinearGroup
variable {F:Type*} [Field F]
private theorem offdiagonal_eq_zero (h2:(2:F)≠0) (A:GL (Fin 2) F)
    (hc:∀u:GL (Fin 2) F,Commute A (u*A*u⁻¹)) :
    A.val 0 1=0 ∧ A.val 1 0=0 := by
  have hre (i j:Fin 2) (hij:i≠j) (k l:Fin 2) :
      (A.val*((1+single i j (1:F))*A.val*(1+single i j (-1:F)))) k l=
      (((1+single i j (1:F))*A.val*(1+single i j (-1:F)))*A.val) k l := by
    let u:=SpecialLinearGroup.toGL (SpecialLinearGroup.transvection hij (1:F))
    have h:=congrArg (fun x:GL (Fin 2) F=>x.val k l) (hc u).eq
    have hu:u.val=1+single i j (1:F) := rfl
    have hui:u⁻¹.val=1+single i j (-1:F) := by
      change ((SpecialLinearGroup.toGL _ )⁻¹).val=_
      rw [←map_inv,SpecialLinearGroup.transvection_inv]
      rfl
    change (A.val*(u.val*A.val*u⁻¹.val)) k l=((u.val*A.val*u⁻¹.val)*A.val) k l at h
    simpa only [hu,hui] using h
  have h01:=hre 1 0 (by decide) 0 1
  have h10:=hre 0 1 (by decide) 1 0
  simp [Matrix.mul_apply,Fin.sum_univ_two] at h01 h10
  have hs01 : 2*(A.val 0 1)^2=0 := by linear_combination h01
  have hs10 : 2*(A.val 1 0)^2=0 := by linear_combination h10
  exact ⟨(sq_eq_zero_iff).mp ((mul_eq_zero.mp hs01).resolve_left h2),
    (sq_eq_zero_iff).mp ((mul_eq_zero.mp hs10).resolve_left h2)⟩

/-- In odd characteristic, a matrix commuting with all its GL₂-conjugates
is scalar. Only the two elementary shears are needed. -/
theorem scalar_of_commutes_conjugates (h2:(2:F)≠0) (A:GL (Fin 2) F)
    (hc:∀u:GL (Fin 2) F,Commute A (u*A*u⁻¹)) :
    A∈(scalar (Fin 2):Fˣ→*GL (Fin 2) F).range := by
  obtain ⟨h01,h10⟩:=offdiagonal_eq_zero h2 A hc
  let u:=SpecialLinearGroup.toGL (SpecialLinearGroup.transvection (show (0:Fin 2)≠1 by decide) (1:F))
  have h:=congrArg (fun x:GL (Fin 2) F=>x.val 0 1) (hc u).eq
  have hu:u.val=1+single 0 1 (1:F) := rfl
  have hui:u⁻¹.val=1+single 0 1 (-1:F) := by
    change ((SpecialLinearGroup.toGL _)⁻¹).val=_
    rw [←map_inv,SpecialLinearGroup.transvection_inv]
    rfl
  change (A.val*(u.val*A.val*u⁻¹.val)) 0 1=((u.val*A.val*u⁻¹.val)*A.val) 0 1 at h
  simp only [hu,hui] at h
  simp [Matrix.mul_apply,Fin.sum_univ_two,h01,h10] at h
  have hs:(A.val 0 0-A.val 1 1)^2=0 := by linear_combination -h
  have hd:A.val 0 0=A.val 1 1 := sub_eq_zero.mp (sq_eq_zero_iff.mp hs)
  have ha:A.val 0 0≠0 := by
    intro ha
    have h:=congrArg (fun x:GL (Fin 2) F=>x.val 0 0) (mul_inv_cancel A)
    change (A.val*A⁻¹.val : Matrix (Fin 2) (Fin 2) F) 0 0=1 at h
    simp only [Matrix.mul_apply,Fin.sum_univ_two,ha,h01,zero_mul,zero_add] at h
    exact zero_ne_one h
  refine ⟨Units.mk0 (A.val 0 0) ha,?_⟩
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [scalar,Matrix.scalar,h01,h10,hd]

/-- Every abelian normal GL₂ subgroup in odd characteristic is scalar,
including over the field of order three. -/
theorem abelian_normal_le_scalar (h2:(2:F)≠0) (A:Subgroup (GL (Fin 2) F))
    [A.Normal] [IsMulCommutative A] : A≤(scalar (Fin 2):Fˣ→*GL (Fin 2) F).range := by
  intro a ha
  apply scalar_of_commutes_conjugates h2 a
  intro u
  exact congrArg Subtype.val (mul_comm (⟨a,ha⟩:A)
    ⟨u*a*u⁻¹,(inferInstance:A.Normal).conj_mem a ha u⟩)
end Matrix.GeneralLinearGroup
