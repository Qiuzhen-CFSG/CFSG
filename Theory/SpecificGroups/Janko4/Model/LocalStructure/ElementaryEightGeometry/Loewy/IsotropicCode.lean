module
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.ElementaryEightGeometry.Loewy.SmallImage

set_option backward.isDefEq.respectTransparency true
public noncomputable section
namespace Janko4.LocalStructure.ElementaryEightGeometry.Loewy
open Subgroup Matrix
open scoped IsMulCommutative
attribute [local irreducible] modelGroup matrixA matrixB

private theorem isotropicCoordinates_formula (v : Fin 4 → ZMod 2) :
    isotropicCoordinates v = eightCoordinates 0
      (![v 0 + v 1 + v 2,v 0,v 1,v 2], ![0,0,0,v 3]) := by
  simp only [isotropicCoordinates,Fintype.linearCombination_apply,eightCoordinates,
    kernelSum,liftSum,Fin.sum_univ_succ,isotropicVector,
    Matrix.cons_val_zero,Matrix.cons_val_succ,Matrix.cons_val_fin_one,
    Fin.sum_univ_zero,add_zero,zero_smul,zero_add,smul_add,add_smul]
  simp only [Fin.succ_zero_eq_one, Fin.succ_one_eq_two, show (2 : Fin 3).succ = 3 from rfl]
  change (v 0 • kernelVector 0 0 + v 0 • kernelVector 0 1) +
      ((v 1 • kernelVector 0 0 + v 1 • kernelVector 0 2) +
        ((v 2 • kernelVector 0 0 + v 2 • kernelVector 0 3) + v 3 • liftVector 0 3)) =
    ((v 0 • kernelVector 0 0 + v 1 • kernelVector 0 0) + v 2 • kernelVector 0 0) +
      (v 0 • kernelVector 0 1 + (v 1 • kernelVector 0 2 + v 2 • kernelVector 0 3)) +
        v 3 • liftVector 0 3
  abel

/-- The concrete zero-form sixteen is exactly the even kernel code with only
its original pair-lift coordinate allowed. -/
theorem coordinates_mem_isotropicSubgroup_iff (a b : Fin 4 → ZMod 2) :
    ((eightCoordinates 0 (a,b)).toMul : Model) ∈ isotropicSubgroup ↔
      a 0 + a 1 + a 2 + a 3 = 0 ∧ b 0 = 0 ∧ b 1 = 0 ∧ b 2 = 0 := by
  have hm : ((eightCoordinates 0 (a,b)).toMul : Model) ∈ isotropicSubgroup ↔
      eightCoordinates 0 (a,b) ∈ isotropicSpace := by
    constructor
    · rintro ⟨x,hx,he⟩
      have hh : Additive.ofMul x = eightCoordinates 0 (a,b) :=
        congrArg Additive.ofMul (Subtype.ext he)
      exact hh ▸ hx
    · intro hx
      exact ⟨(eightCoordinates 0 (a,b)).toMul,hx,rfl⟩
  rw [hm,← isotropicCoordinates_range]
  constructor
  · rintro ⟨v,hv⟩
    rw [isotropicCoordinates_formula] at hv
    have he := eightCoordinates_injective 0 hv
    have ha : a = ![v 0 + v 1 + v 2,v 0,v 1,v 2] := (congrArg Prod.fst he).symm
    have hb : b = ![0,0,0,v 3] := (congrArg Prod.snd he).symm
    rw [ha,hb]
    refine ⟨?_,rfl,rfl,rfl⟩
    change (v 0 + v 1 + v 2) + v 0 + v 1 + v 2 = 0
    have hz (x : ZMod 2) : x+x=0 := CharTwo.add_self_eq_zero x
    linear_combination hz (v 0) + hz (v 1) + hz (v 2)
  · rintro ⟨ha,hb0,hb1,hb2⟩
    refine ⟨![a 1,a 2,a 3,b 3],?_⟩
    rw [isotropicCoordinates_formula]
    congr 1
    apply Prod.ext
    · funext i
      fin_cases i
      · change a 1 + a 2 + a 3 = a 0
        have hz (x : ZMod 2) : x+x=0 := CharTwo.add_self_eq_zero x
        linear_combination ha - hz (a 0)
      · rfl
      · rfl
      · rfl
    · funext i
      fin_cases i <;> simp [hb0,hb1,hb2]

end Janko4.LocalStructure.ElementaryEightGeometry.Loewy
