module

public import Theory.SpecificGroups.ReeF4.LocalBlockInput.OuterOddSubgroups.PairRigidity.BlockGeometry.ParabolicRecognition.LocalIndices.SuzukiCover.Gauss.Ambient.Calculation.CartanBlock.Weyl
/-!
# The two nonsimple signed roots on the Cartan block

The high and mixed B₂ root matrices are obtained by the literal simple Weyl
conjugations from `Blocks`. Two sparse products verify each conjugation on all
12 coordinates, preserving the Cartan columns.

Source: GLS3, 2.3.4--8 and Table 2.4 type V,
`refs/KGroup/GLS3/chapter2.tex`; the signed supports in `Ambient.Tables`.
-/

namespace ReeF4.LocalBlockInput.PairRigidity.LocalIndices.SuzukiGaussData.Ambient.Calculation.CartanBlock
open BlockParameters.FieldRecovery
open scoped Matrix
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
variable {m : ℕ}

private def rootLeft_true_2 (t : CoefficientField m) : Matrix (Fin 12) (Fin 12) (CoefficientField m) :=
  !![1,0,0,0,0,0,0,0,0,0,0,0;
      0,1,0,0,0,0,t,0,0,0,0,0;
      0,1,1,1,0,0,t,0,0,0,0,0;
      0,0,0,1,0,0,0,0,0,0,0,0;
      0,0,0,0,0,0,1,0,0,0,0,0;
      0,0,0,0,0,1,0,0,0,0,0,0;
      0,0,0,0,1,0,0,0,0,0,0,0;
      0,0,0,0,0,0,0,0,1,0,0,0;
      0,0,0,0,0,t,0,1,0,0,0,0;
      0,0,0,0,0,0,0,0,0,0,0,1;
      0,0,0,0,0,0,0,0,t,0,1,0;
      t,0,0,0,0,0,t ^ 2,0,0,1,0,0]

private lemma rootLeft_true_2_eq (t : CoefficientField m) :
    reflection_1 * simple_true_0 t = rootLeft_true_2 t := by
  ext r c
  try simp only [Matrix.mul_apply]
  fin_cases r <;>
    simp [reflection_1, simple_true_0, rootLeft_true_2, Matrix.mul_apply,
      Matrix.vecMul, dotProduct, Fin.sum_univ_succ, CharTwo.add_self_eq_zero]
  all_goals fin_cases c <;> simp [CharTwo.add_self_eq_zero]

def root_true_2 (t : CoefficientField m) : Matrix (Fin 12) (Fin 12) (CoefficientField m) :=
  !![1,0,0,0,0,0,0,0,0,0,0,0;
      0,1,0,0,t,0,0,0,0,0,0,0;
      0,0,1,0,t,0,0,0,0,0,0,0;
      0,0,0,1,0,0,0,0,0,0,0,0;
      0,0,0,0,1,0,0,0,0,0,0,0;
      0,0,0,0,0,1,0,0,0,0,0,0;
      0,0,0,0,0,0,1,0,0,0,0,0;
      0,0,0,0,0,0,0,1,0,0,0,0;
      0,0,0,0,0,t,0,0,1,0,0,0;
      0,0,0,0,0,0,0,0,0,1,0,0;
      0,0,0,0,0,0,0,t,0,0,1,0;
      t,0,0,0,t ^ 2,0,0,0,0,0,0,1]

private lemma root_true_2_literal (t : CoefficientField m) :
    rootLeft_true_2 t * reflection_1 = root_true_2 t := by
  ext r c
  try simp only [Matrix.mul_apply]
  fin_cases r <;>
    simp [rootLeft_true_2, reflection_1, root_true_2, Matrix.mul_apply,
      Matrix.vecMul, dotProduct, Fin.sum_univ_succ, CharTwo.add_self_eq_zero]
  all_goals fin_cases c <;> simp [CharTwo.add_self_eq_zero]

lemma root_true_2_eq (t : CoefficientField m) :
    blockRoot 0 true 2 t = root_true_2 t := by
  change blockReflection 0 1 * blockSimple 0 true 0 t * blockReflection 0 1 = _
  rw [reflection_1_eq, simple_true_0_eq, rootLeft_true_2_eq, root_true_2_literal]

private def rootLeft_true_3 (t : CoefficientField m) : Matrix (Fin 12) (Fin 12) (CoefficientField m) :=
  !![1,0,0,0,0,0,0,0,0,0,0,0;
      1,1,0,0,0,0,0,0,0,0,0,0;
      0,0,1,0,0,0,0,t,0,0,0,0;
      0,0,0,1,0,0,0,0,0,0,0,0;
      0,0,0,0,1,0,0,0,0,0,0,0;
      0,0,0,0,0,0,0,1,0,0,0,0;
      0,0,0,0,0,0,0,0,0,1,0,0;
      0,0,0,0,t,1,0,0,0,0,0,0;
      0,0,0,0,0,0,0,0,0,t,1,0;
      0,0,0,0,t ^ 2,0,1,0,0,0,0,0;
      0,t,0,t,0,0,0,t ^ 2,1,0,0,0;
      0,0,0,0,0,0,0,0,0,t ^ 2,0,1]

private lemma rootLeft_true_3_eq (t : CoefficientField m) :
    reflection_0 * simple_true_1 t = rootLeft_true_3 t := by
  ext r c
  try simp only [Matrix.mul_apply]
  fin_cases r <;>
    simp [reflection_0, simple_true_1, rootLeft_true_3, Matrix.mul_apply,
      Matrix.vecMul, dotProduct, Fin.sum_univ_succ, CharTwo.add_self_eq_zero]
  all_goals fin_cases c <;> simp [CharTwo.add_self_eq_zero]

def root_true_3 (t : CoefficientField m) : Matrix (Fin 12) (Fin 12) (CoefficientField m) :=
  !![1,0,0,0,0,0,0,0,0,0,0,0;
      0,1,0,0,0,0,0,0,0,0,0,0;
      0,0,1,0,0,t,0,0,0,0,0,0;
      0,0,0,1,0,0,0,0,0,0,0,0;
      0,0,0,0,1,0,0,0,0,0,0,0;
      0,0,0,0,0,1,0,0,0,0,0,0;
      0,0,0,0,0,0,1,0,0,0,0,0;
      0,0,0,0,t,0,0,1,0,0,0,0;
      0,0,0,0,0,0,t,0,1,0,0,0;
      0,0,0,0,t ^ 2,0,0,0,0,1,0,0;
      t,t,0,t,0,t ^ 2,0,0,0,0,1,0;
      0,0,0,0,0,0,t ^ 2,0,0,0,0,1]

private lemma root_true_3_literal (t : CoefficientField m) :
    rootLeft_true_3 t * reflection_0 = root_true_3 t := by
  ext r c
  try simp only [Matrix.mul_apply]
  fin_cases r <;>
    simp [rootLeft_true_3, reflection_0, root_true_3, Matrix.mul_apply,
      Matrix.vecMul, dotProduct, Fin.sum_univ_succ, CharTwo.add_self_eq_zero]
  all_goals fin_cases c <;> simp [CharTwo.add_self_eq_zero]

lemma root_true_3_eq (t : CoefficientField m) :
    blockRoot 0 true 3 t = root_true_3 t := by
  change blockReflection 0 0 * blockSimple 0 true 1 t * blockReflection 0 0 = _
  rw [reflection_0_eq, simple_true_1_eq, rootLeft_true_3_eq, root_true_3_literal]

private def rootLeft_false_2 (t : CoefficientField m) : Matrix (Fin 12) (Fin 12) (CoefficientField m) :=
  !![1,0,0,0,0,0,0,0,0,0,0,0;
      0,1,0,0,0,0,0,0,0,t,0,0;
      0,1,1,1,0,0,0,0,0,t,0,0;
      0,0,0,1,0,0,0,0,0,0,0,0;
      t,0,0,0,0,0,1,0,0,t ^ 2,0,0;
      0,0,0,0,0,1,0,t,0,0,0,0;
      0,0,0,0,1,0,0,0,0,0,0,0;
      0,0,0,0,0,0,0,0,1,0,t,0;
      0,0,0,0,0,0,0,1,0,0,0,0;
      0,0,0,0,0,0,0,0,0,0,0,1;
      0,0,0,0,0,0,0,0,0,0,1,0;
      0,0,0,0,0,0,0,0,0,1,0,0]

private lemma rootLeft_false_2_eq (t : CoefficientField m) :
    reflection_1 * simple_false_0 t = rootLeft_false_2 t := by
  ext r c
  try simp only [Matrix.mul_apply]
  fin_cases r <;>
    simp [reflection_1, simple_false_0, rootLeft_false_2, Matrix.mul_apply,
      Matrix.vecMul, dotProduct, Fin.sum_univ_succ, CharTwo.add_self_eq_zero]
  all_goals fin_cases c <;> simp [CharTwo.add_self_eq_zero]

def root_false_2 (t : CoefficientField m) : Matrix (Fin 12) (Fin 12) (CoefficientField m) :=
  !![1,0,0,0,0,0,0,0,0,0,0,0;
      0,1,0,0,0,0,0,0,0,0,0,t;
      0,0,1,0,0,0,0,0,0,0,0,t;
      0,0,0,1,0,0,0,0,0,0,0,0;
      t,0,0,0,1,0,0,0,0,0,0,t ^ 2;
      0,0,0,0,0,1,0,0,t,0,0,0;
      0,0,0,0,0,0,1,0,0,0,0,0;
      0,0,0,0,0,0,0,1,0,0,t,0;
      0,0,0,0,0,0,0,0,1,0,0,0;
      0,0,0,0,0,0,0,0,0,1,0,0;
      0,0,0,0,0,0,0,0,0,0,1,0;
      0,0,0,0,0,0,0,0,0,0,0,1]

private lemma root_false_2_literal (t : CoefficientField m) :
    rootLeft_false_2 t * reflection_1 = root_false_2 t := by
  ext r c
  try simp only [Matrix.mul_apply]
  fin_cases r <;>
    simp [rootLeft_false_2, reflection_1, root_false_2, Matrix.mul_apply,
      Matrix.vecMul, dotProduct, Fin.sum_univ_succ, CharTwo.add_self_eq_zero]
  all_goals fin_cases c <;> simp [CharTwo.add_self_eq_zero]

lemma root_false_2_eq (t : CoefficientField m) :
    blockRoot 0 false 2 t = root_false_2 t := by
  change blockReflection 0 1 * blockSimple 0 false 0 t * blockReflection 0 1 = _
  rw [reflection_1_eq, simple_false_0_eq, rootLeft_false_2_eq, root_false_2_literal]

private def rootLeft_false_3 (t : CoefficientField m) : Matrix (Fin 12) (Fin 12) (CoefficientField m) :=
  !![1,0,0,0,0,0,0,0,0,0,0,0;
      1,1,0,0,0,0,0,0,0,0,0,0;
      0,0,1,0,0,0,0,0,t,0,0,0;
      0,0,0,1,0,0,0,0,0,0,0,0;
      0,0,0,0,1,0,t ^ 2,0,0,0,0,0;
      0,t,0,t,0,0,0,1,t ^ 2,0,0,0;
      0,0,0,0,0,0,0,0,0,1,0,t ^ 2;
      0,0,0,0,0,1,t,0,0,0,0,0;
      0,0,0,0,0,0,0,0,0,0,1,t;
      0,0,0,0,0,0,1,0,0,0,0,0;
      0,0,0,0,0,0,0,0,1,0,0,0;
      0,0,0,0,0,0,0,0,0,0,0,1]

private lemma rootLeft_false_3_eq (t : CoefficientField m) :
    reflection_0 * simple_false_1 t = rootLeft_false_3 t := by
  ext r c
  try simp only [Matrix.mul_apply]
  fin_cases r <;>
    simp [reflection_0, simple_false_1, rootLeft_false_3, Matrix.mul_apply,
      Matrix.vecMul, dotProduct, Fin.sum_univ_succ, CharTwo.add_self_eq_zero]
  all_goals fin_cases c <;> simp [CharTwo.add_self_eq_zero]

def root_false_3 (t : CoefficientField m) : Matrix (Fin 12) (Fin 12) (CoefficientField m) :=
  !![1,0,0,0,0,0,0,0,0,0,0,0;
      0,1,0,0,0,0,0,0,0,0,0,0;
      0,0,1,0,0,0,0,0,0,0,t,0;
      0,0,0,1,0,0,0,0,0,0,0,0;
      0,0,0,0,1,0,0,0,0,t ^ 2,0,0;
      t,t,0,t,0,1,0,0,0,0,t ^ 2,0;
      0,0,0,0,0,0,1,0,0,0,0,t ^ 2;
      0,0,0,0,0,0,0,1,0,t,0,0;
      0,0,0,0,0,0,0,0,1,0,0,t;
      0,0,0,0,0,0,0,0,0,1,0,0;
      0,0,0,0,0,0,0,0,0,0,1,0;
      0,0,0,0,0,0,0,0,0,0,0,1]

private lemma root_false_3_literal (t : CoefficientField m) :
    rootLeft_false_3 t * reflection_0 = root_false_3 t := by
  ext r c
  try simp only [Matrix.mul_apply]
  fin_cases r <;>
    simp [rootLeft_false_3, reflection_0, root_false_3, Matrix.mul_apply,
      Matrix.vecMul, dotProduct, Fin.sum_univ_succ, CharTwo.add_self_eq_zero]
  all_goals fin_cases c <;> simp [CharTwo.add_self_eq_zero]

lemma root_false_3_eq (t : CoefficientField m) :
    blockRoot 0 false 3 t = root_false_3 t := by
  change blockReflection 0 0 * blockSimple 0 false 1 t * blockReflection 0 0 = _
  rw [reflection_0_eq, simple_false_1_eq, rootLeft_false_3_eq, root_false_3_literal]

end
end ReeF4.LocalBlockInput.PairRigidity.LocalIndices.SuzukiGaussData.Ambient.Calculation.CartanBlock
