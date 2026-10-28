module

public import Theory.SpecificGroups.ReeF4.LocalBlockInput.OuterOddSubgroups.PairRigidity.BlockGeometry.ParabolicRecognition.LocalIndices.SuzukiCover.Gauss.Ambient.Calculation.CartanBlock.Simple
/-!
# Literal Weyl representatives on the Cartan block

Multiplying each signed simple pair and then its third root factor gives the
parameter-dependent Weyl matrices. Specializing the parameter to one supplies
the two reflections, including their nontrivial Cartan entries. The staged
entry calculations avoid expanding a triple matrix product in every cell.

Source: GLS3, 2.3.4--8 and Table 2.4 type V,
`refs/KGroup/GLS3/chapter2.tex`; the supports checked in `CartanBlock.Simple`.
-/

namespace ReeF4.LocalBlockInput.PairRigidity.LocalIndices.SuzukiGaussData.Ambient.Calculation.CartanBlock
open BlockParameters.FieldRecovery
open scoped Matrix
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
variable {m : ℕ}
private def weylPair_0 (t z : CoefficientField m) : Matrix (Fin 12) (Fin 12) (CoefficientField m) :=
  !![1,0,0,0,0,0,0,0,0,0,0,0;
      (t * z),1,0,0,0,0,t,0,0,(z + (t * z ^ 2)),0,0;
      0,0,1,0,0,0,0,0,0,0,0,0;
      0,0,0,1,0,0,0,0,0,0,0,0;
      0,0,0,0,1,0,0,0,0,0,0,0;
      0,0,0,0,0,1,0,z,0,0,0,0;
      z,0,0,0,0,0,1,0,0,z ^ 2,0,0;
      0,0,0,0,0,t,0,(1 + (t * z)),0,0,0,0;
      0,0,0,0,0,0,0,0,1,0,z,0;
      (t + (z * t ^ 2)),0,0,0,0,0,t ^ 2,0,0,(1 + (t ^ 2 * z ^ 2)),0,0;
      0,0,0,0,0,0,0,0,t,0,(1 + (t * z)),0;
      0,0,0,0,0,0,0,0,0,0,0,1]

private lemma weylPair_0_eq (t z : CoefficientField m) :
    simple_true_0 t * simple_false_0 z = weylPair_0 t z := by
  ext r c
  simp only [Matrix.mul_apply]
  fin_cases r <;>
    simp [simple_true_0, simple_false_0, weylPair_0, Matrix.mul_apply,
      Matrix.vecMul, dotProduct, Fin.sum_univ_succ]
  all_goals try fin_cases c <;> simp
  all_goals ring_nf

def weyl_0 (t : CoefficientField m) : Matrix (Fin 12) (Fin 12) (CoefficientField m) :=
  !![1,0,0,0,0,0,0,0,0,0,0,0;
      1,1,0,0,0,0,0,0,0,0,0,0;
      0,0,1,0,0,0,0,0,0,0,0,0;
      0,0,0,1,0,0,0,0,0,0,0,0;
      0,0,0,0,1,0,0,0,0,0,0,0;
      0,0,0,0,0,0,0,t⁻¹,0,0,0,0;
      0,0,0,0,0,0,0,0,0,t⁻¹ ^ 2,0,0;
      0,0,0,0,0,t,0,0,0,0,0,0;
      0,0,0,0,0,0,0,0,0,0,t⁻¹,0;
      0,0,0,0,0,0,t ^ 2,0,0,0,0,0;
      0,0,0,0,0,0,0,0,t,0,0,0;
      0,0,0,0,0,0,0,0,0,0,0,1]

private lemma weyl_0_literal (t : CoefficientField m) (ht : t ≠ 0) :
    weylPair_0 t t⁻¹ * simple_true_0 t = weyl_0 t := by
  ext r c
  simp only [Matrix.mul_apply]
  fin_cases r <;>
    simp [weylPair_0, simple_true_0, weyl_0, Matrix.mul_apply,
      Matrix.vecMul, dotProduct, Fin.sum_univ_succ, ht, CharTwo.add_self_eq_zero]
  all_goals fin_cases c <;> simp [ht, CharTwo.add_self_eq_zero]
  all_goals field_simp
  all_goals ring_nf
  all_goals simp [CharTwo.ofNat_eq_mod]

lemma weyl_0_eq (t : CoefficientField m) (ht : t ≠ 0) :
    blockWeyl 0 0 t = weyl_0 t := by
  rw [blockWeyl, simple_true_0_eq, simple_false_0_eq, weylPair_0_eq,
    weyl_0_literal t ht]

def reflection_0 : Matrix (Fin 12) (Fin 12) (CoefficientField m) :=
  !![1,0,0,0,0,0,0,0,0,0,0,0;
      1,1,0,0,0,0,0,0,0,0,0,0;
      0,0,1,0,0,0,0,0,0,0,0,0;
      0,0,0,1,0,0,0,0,0,0,0,0;
      0,0,0,0,1,0,0,0,0,0,0,0;
      0,0,0,0,0,0,0,1,0,0,0,0;
      0,0,0,0,0,0,0,0,0,1,0,0;
      0,0,0,0,0,1,0,0,0,0,0,0;
      0,0,0,0,0,0,0,0,0,0,1,0;
      0,0,0,0,0,0,1,0,0,0,0,0;
      0,0,0,0,0,0,0,0,1,0,0,0;
      0,0,0,0,0,0,0,0,0,0,0,1]

lemma reflection_0_eq :
    blockReflection (R := CoefficientField m) 0 0 = reflection_0 := by
  rw [blockReflection, weyl_0_eq 1 one_ne_zero]
  simp [weyl_0, reflection_0]

private def weylPair_1 (t z : CoefficientField m) : Matrix (Fin 12) (Fin 12) (CoefficientField m) :=
  !![1,0,0,0,0,0,0,0,0,0,0,0;
      0,1,0,0,0,0,0,0,0,0,0,0;
      0,(t * z),1,(t * z),0,0,0,t,(z + (t * z ^ 2)),0,0,0;
      0,0,0,1,0,0,0,0,0,0,0,0;
      0,0,0,0,1,0,z ^ 2,0,0,0,0,0;
      0,0,0,0,t,1,(z + (t * z ^ 2)),0,0,0,0,0;
      0,0,0,0,t ^ 2,0,(1 + (t ^ 2 * z ^ 2)),0,0,0,0,0;
      0,z,0,z,0,0,0,1,z ^ 2,0,0,0;
      0,(t + (z * t ^ 2)),0,(t + (z * t ^ 2)),0,0,0,t ^ 2,(1 + (t ^ 2 * z ^ 2)),0,0,0;
      0,0,0,0,0,0,0,0,0,1,0,z ^ 2;
      0,0,0,0,0,0,0,0,0,t,1,(z + (t * z ^ 2));
      0,0,0,0,0,0,0,0,0,t ^ 2,0,(1 + (t ^ 2 * z ^ 2))]

private lemma weylPair_1_eq (t z : CoefficientField m) :
    simple_true_1 t * simple_false_1 z = weylPair_1 t z := by
  ext r c
  simp only [Matrix.mul_apply]
  fin_cases r <;>
    simp [simple_true_1, simple_false_1, weylPair_1, Matrix.mul_apply,
      Matrix.vecMul, dotProduct, Fin.sum_univ_succ]
  all_goals try fin_cases c <;> simp
  all_goals ring_nf

def weyl_1 (t : CoefficientField m) : Matrix (Fin 12) (Fin 12) (CoefficientField m) :=
  !![1,0,0,0,0,0,0,0,0,0,0,0;
      0,1,0,0,0,0,0,0,0,0,0,0;
      0,1,1,1,0,0,0,0,0,0,0,0;
      0,0,0,1,0,0,0,0,0,0,0,0;
      0,0,0,0,0,0,t⁻¹ ^ 2,0,0,0,0,0;
      0,0,0,0,0,1,0,0,0,0,0,0;
      0,0,0,0,t ^ 2,0,0,0,0,0,0,0;
      0,0,0,0,0,0,0,0,t⁻¹ ^ 2,0,0,0;
      0,0,0,0,0,0,0,t ^ 2,0,0,0,0;
      0,0,0,0,0,0,0,0,0,0,0,t⁻¹ ^ 2;
      0,0,0,0,0,0,0,0,0,0,1,0;
      0,0,0,0,0,0,0,0,0,t ^ 2,0,0]

private lemma weyl_1_literal (t : CoefficientField m) (ht : t ≠ 0) :
    weylPair_1 t t⁻¹ * simple_true_1 t = weyl_1 t := by
  ext r c
  simp only [Matrix.mul_apply]
  fin_cases r <;>
    simp [weylPair_1, simple_true_1, weyl_1, Matrix.mul_apply,
      Matrix.vecMul, dotProduct, Fin.sum_univ_succ, ht, CharTwo.add_self_eq_zero]
  all_goals fin_cases c <;> simp [ht, CharTwo.add_self_eq_zero]
  all_goals field_simp
  all_goals ring_nf
  all_goals simp [CharTwo.ofNat_eq_mod]

lemma weyl_1_eq (t : CoefficientField m) (ht : t ≠ 0) :
    blockWeyl 0 1 t = weyl_1 t := by
  rw [blockWeyl, simple_true_1_eq, simple_false_1_eq, weylPair_1_eq,
    weyl_1_literal t ht]

def reflection_1 : Matrix (Fin 12) (Fin 12) (CoefficientField m) :=
  !![1,0,0,0,0,0,0,0,0,0,0,0;
      0,1,0,0,0,0,0,0,0,0,0,0;
      0,1,1,1,0,0,0,0,0,0,0,0;
      0,0,0,1,0,0,0,0,0,0,0,0;
      0,0,0,0,0,0,1,0,0,0,0,0;
      0,0,0,0,0,1,0,0,0,0,0,0;
      0,0,0,0,1,0,0,0,0,0,0,0;
      0,0,0,0,0,0,0,0,1,0,0,0;
      0,0,0,0,0,0,0,1,0,0,0,0;
      0,0,0,0,0,0,0,0,0,0,0,1;
      0,0,0,0,0,0,0,0,0,0,1,0;
      0,0,0,0,0,0,0,0,0,1,0,0]

lemma reflection_1_eq :
    blockReflection (R := CoefficientField m) 0 1 = reflection_1 := by
  rw [blockReflection, weyl_1_eq 1 one_ne_zero]
  simp [weyl_1, reflection_1]

end
end ReeF4.LocalBlockInput.PairRigidity.LocalIndices.SuzukiGaussData.Ambient.Calculation.CartanBlock
