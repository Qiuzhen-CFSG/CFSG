module

public import Theory.SpecificGroups.ReeF4.LocalBlockInput.OuterOddSubgroups.PairRigidity.BlockGeometry.ParabolicRecognition.LocalIndices.SuzukiCover.Gauss.Ambient.Calculation.Blocks
public import Theory.SpecificGroups.ReeF4.LocalBlockInput.OuterOddSubgroups.PairRigidity.BlockGeometry.ParabolicRecognition.LocalIndices.SuzukiCover.Gauss.FourDimensional
/-!
# Gauss identity on the four-dimensional coordinate blocks

Reversing the four coordinates identifies block 5 with the existing elementary
four-dimensional model. The comparisons retain both signs, arbitrary parameters,
the exact Weyl conjugations for the high and mixed roots, and both coroots.
Applying this full matrix algebra equivalence to `four_gauss` proves the block
equation. `Calculation.Repeated` handles the other three identical blocks.

Source: GLS3, Table 2.4 type V and 2.3.4--8,
`refs/KGroup/GLS3/chapter2.tex`; the scalar factorization in `Gauss.FourDimensional`.
-/

namespace ReeF4.LocalBlockInput.PairRigidity.LocalIndices.SuzukiGaussData.Ambient.Calculation
open BlockParameters.FieldRecovery BenderSuzuki.MatrixGroups
open scoped Matrix
noncomputable section
variable {m : ℕ}

def fourMap (m : ℕ) : Matrix (Fin 4) (Fin 4) (CoefficientField m) ≃+*
    Matrix (Fin (blockSize 5)) (Fin (blockSize 5)) (CoefficientField m) :=
  Matrix.reindexRingEquiv _ (Fin.revPerm.trans (finCongr (by decide : 4 = blockSize 5)))

lemma blockSimple_five (p : Bool) (i : Fin 2) (t : CoefficientField m) :
    blockSimple 5 p i t = fourMap m (fourRoot p (Fin.castLE (by decide : 2 ≤ 4) i) t) := by
  ext r c
  change simpleMatrix p i t (blockCoord 5 r) (blockCoord 5 c) =
    fourRoot p (Fin.castLE (by decide : 2 ≤ 4) i) t (Fin.rev r) (Fin.rev c)
  cases p <;> fin_cases i <;> fin_cases r <;> fin_cases c <;>
    simp [blockCoord, simpleMatrix, simpleIndex, incidence, linearSupport,
      quadraticSupport, fourRoot, Fin.rev]

lemma blockWeyl_five (i : Fin 2) (t : CoefficientField m) :
    blockWeyl 5 i t = fourMap m (fourWeyl i t) := by
  simp only [blockWeyl, fourWeyl, blockSimple_five, map_mul]

lemma blockReflection_five (i : Fin 2) :
    blockReflection (R := CoefficientField m) 5 i = fourMap m (fourWeyl i 1) :=
  blockWeyl_five i 1

lemma fourWeyl_long_matrix :
    fourWeyl (m := m) 0 1 = !![1,0,0,0; 0,0,1,0; 0,1,0,0; 0,0,0,1] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [fourWeyl, fourRoot, Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_four,
      CharTwo.add_self_eq_zero]

lemma fourWeyl_short_matrix :
    fourWeyl (m := m) 1 1 = !![0,1,0,0; 1,0,0,0; 0,0,0,1; 0,0,1,0] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [fourWeyl, fourRoot, Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_four,
      CharTwo.add_self_eq_zero]

lemma fourRoot_high_conjugate (p : Bool) (t : CoefficientField m) :
    fourWeyl 1 1 * fourRoot p 0 t * fourWeyl 1 1 = fourRoot p 2 t := by
  rw [fourWeyl_short_matrix]
  cases p <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [fourRoot, Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_four]

lemma fourRoot_mixed_conjugate (p : Bool) (t : CoefficientField m) :
    fourWeyl 0 1 * fourRoot p 1 t * fourWeyl 0 1 = fourRoot p 3 t := by
  rw [fourWeyl_long_matrix]
  cases p <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [fourRoot, Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_four]

lemma blockRoot_five (p : Bool) (i : Fin 4) (t : CoefficientField m) :
    blockRoot 5 p i t = fourMap m (fourRoot p i t) := by
  fin_cases i
  · exact blockSimple_five p 0 t
  · exact blockSimple_five p 1 t
  · change blockReflection 5 1 * blockSimple 5 p 0 t * blockReflection 5 1 = _
    rw [blockReflection_five, blockSimple_five, ← map_mul, ← map_mul]
    exact congrArg (fourMap m) (fourRoot_high_conjugate p t)
  · change blockReflection 5 0 * blockSimple 5 p 1 t * blockReflection 5 0 = _
    rw [blockReflection_five, blockSimple_five, ← map_mul, ← map_mul]
    exact congrArg (fourMap m) (fourRoot_mixed_conjugate p t)

lemma blockWord_five (p : Bool) (t u : CoefficientField m) :
    blockWord 5 p t u = fourMap m (fourWord p t u) := by
  simp only [blockWord, fourWord, blockRoot_five, map_mul]

lemma blockPanel_five : blockPanel (R := CoefficientField m) 5 =
    fourMap m (SuzukiWeylMatrix m) := by
  simp only [blockPanel, blockReflection_five, ← map_mul, four_panel_weyl]

lemma blockTorus_five (n : (CoefficientField m)ˣ) :
    blockTorus 5 n = fourMap m (fourTorus (n : CoefficientField m)) := by
  rw [fourTorus_eq_coroots]
  simp only [blockTorus, blockWeyl_five, blockReflection_five, map_mul, fourCoroot]
  rfl

public lemma blockGauss_fourDimensional (m : ℕ) : BlockGauss m 5 := by
  intro t u hn
  simp only [blockPanel_five, blockWord_five, blockTorus_five, ← map_mul]
  exact congrArg (fourMap m) (four_gauss t u hn)
end
end ReeF4.LocalBlockInput.PairRigidity.LocalIndices.SuzukiGaussData.Ambient.Calculation
