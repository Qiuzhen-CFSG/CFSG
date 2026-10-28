module
public import Theory.SpecificGroups.Triality.SimplyConnectedModel.PinningTorus.PointGeneration.CoordinateActions
public import Theory.SpecificGroups.Triality.SimplyConnectedModel.PinningTorus.PointGeneration.RootTable

/-!
# Root matrices under the four pinned Weyl permutations

The coordinate normalizers permute the elementary transvections exactly as
specified by the checked D4 reflection table. The calculation takes place in
the eight-dimensional natural space; faithfulness lifts it to Spin in `Weyl`.
Signs disappear precisely through the characteristic-two hypothesis.

Source: GLS3, Chapter 1, Theorem 1.12.1(h).
-/

@[expose] public section
noncomputable section
namespace Triality.SimplyConnected.Pinning.PointGeneration
open Theory.AlgebraicGroup Theory.AlgebraicGroup.StandardRootSystem
set_option linter.unusedSimpArgs false
universe u
variable (k : Type u) [Field k] [CharP k 2]

private theorem rootAction_conjugation_0 (r : Fin 24) (a : k) (z : HyperbolicSpace k 4) :
    simpleAction k 0 (rootAction k (rootAt r) a (simpleAction k 0 z)) =
      rootAction k (rootAt (reflectionIndex 0 r)) a z := by
  fin_cases r
  all_goals
    dsimp [rootAt, reflectionIndex, simpleAction, rootAction]
    simp only [show (-1 : ℝ) ≠ 1 by norm_num, ↓reduceIte]
    apply Prod.ext <;> funext p <;> fin_cases p <;>
      simp [Matrix.vecHead, Matrix.vecTail, Pi.single_apply, CharTwo.neg_eq,
        sub_eq_add_neg, Fin.ext_iff]

private theorem rootAction_conjugation_1 (r : Fin 24) (a : k) (z : HyperbolicSpace k 4) :
    simpleAction k 1 (rootAction k (rootAt r) a (simpleAction k 1 z)) =
      rootAction k (rootAt (reflectionIndex 1 r)) a z := by
  fin_cases r
  all_goals
    dsimp [rootAt, reflectionIndex, simpleAction, rootAction]
    simp only [show (-1 : ℝ) ≠ 1 by norm_num, ↓reduceIte]
    apply Prod.ext <;> funext p <;> fin_cases p <;>
      simp [Matrix.vecHead, Matrix.vecTail, Pi.single_apply, CharTwo.neg_eq,
        sub_eq_add_neg, Fin.ext_iff]

-- Splitting by the six coordinate supports avoids the global `dsimp`
-- simproc failure on the last two normalizers, while keeping the default heartbeat bound.

private theorem rootAction_conjugation_2_01 (r : Fin 4) (a : k)
    (z : HyperbolicSpace k 4) :
    simpleAction k 2 (rootAction k (rootAt ⟨r.val + 0, by omega⟩) a (simpleAction k 2 z)) =
      rootAction k (rootAt (reflectionIndex 2 ⟨r.val + 0, by omega⟩)) a z := by
  fin_cases r
  all_goals
    norm_num [rootAt, reflectionIndex, rootAction]
    apply Prod.ext <;> funext p <;> fin_cases p <;>
      simp [show (-1 : ℝ) ≠ 1 by norm_num, simpleAction, Matrix.vecHead,
        Matrix.vecTail, Pi.single_apply, CharTwo.neg_eq, sub_eq_add_neg, Fin.ext_iff]

private theorem rootAction_conjugation_2_02 (r : Fin 4) (a : k)
    (z : HyperbolicSpace k 4) :
    simpleAction k 2 (rootAction k (rootAt ⟨r.val + 4, by omega⟩) a (simpleAction k 2 z)) =
      rootAction k (rootAt (reflectionIndex 2 ⟨r.val + 4, by omega⟩)) a z := by
  fin_cases r
  all_goals
    norm_num [rootAt, reflectionIndex, rootAction]
    apply Prod.ext <;> funext p <;> fin_cases p <;>
      simp [show (-1 : ℝ) ≠ 1 by norm_num, simpleAction, Matrix.vecHead,
        Matrix.vecTail, Pi.single_apply, CharTwo.neg_eq, sub_eq_add_neg, Fin.ext_iff]

private theorem rootAction_conjugation_2_03 (r : Fin 4) (a : k)
    (z : HyperbolicSpace k 4) :
    simpleAction k 2 (rootAction k (rootAt ⟨r.val + 8, by omega⟩) a (simpleAction k 2 z)) =
      rootAction k (rootAt (reflectionIndex 2 ⟨r.val + 8, by omega⟩)) a z := by
  fin_cases r
  all_goals
    norm_num [rootAt, reflectionIndex, rootAction]
    apply Prod.ext <;> funext p <;> fin_cases p <;>
      simp [show (-1 : ℝ) ≠ 1 by norm_num, simpleAction, Matrix.vecHead,
        Matrix.vecTail, Pi.single_apply, CharTwo.neg_eq, sub_eq_add_neg, Fin.ext_iff]

private theorem rootAction_conjugation_2_12 (r : Fin 4) (a : k)
    (z : HyperbolicSpace k 4) :
    simpleAction k 2 (rootAction k (rootAt ⟨r.val + 12, by omega⟩) a (simpleAction k 2 z)) =
      rootAction k (rootAt (reflectionIndex 2 ⟨r.val + 12, by omega⟩)) a z := by
  fin_cases r
  all_goals
    norm_num [rootAt, reflectionIndex, rootAction]
    apply Prod.ext <;> funext p <;> fin_cases p <;>
      simp [show (-1 : ℝ) ≠ 1 by norm_num, simpleAction, Matrix.vecHead,
        Matrix.vecTail, Pi.single_apply, CharTwo.neg_eq, sub_eq_add_neg, Fin.ext_iff]

private theorem rootAction_conjugation_2_13 (r : Fin 4) (a : k)
    (z : HyperbolicSpace k 4) :
    simpleAction k 2 (rootAction k (rootAt ⟨r.val + 16, by omega⟩) a (simpleAction k 2 z)) =
      rootAction k (rootAt (reflectionIndex 2 ⟨r.val + 16, by omega⟩)) a z := by
  fin_cases r
  all_goals
    norm_num [rootAt, reflectionIndex, rootAction]
    apply Prod.ext <;> funext p <;> fin_cases p <;>
      simp [show (-1 : ℝ) ≠ 1 by norm_num, simpleAction, Matrix.vecHead,
        Matrix.vecTail, Pi.single_apply, CharTwo.neg_eq, sub_eq_add_neg, Fin.ext_iff]

private theorem rootAction_conjugation_2_23 (r : Fin 4) (a : k)
    (z : HyperbolicSpace k 4) :
    simpleAction k 2 (rootAction k (rootAt ⟨r.val + 20, by omega⟩) a (simpleAction k 2 z)) =
      rootAction k (rootAt (reflectionIndex 2 ⟨r.val + 20, by omega⟩)) a z := by
  fin_cases r
  all_goals
    norm_num [rootAt, reflectionIndex, rootAction]
    apply Prod.ext <;> funext p <;> fin_cases p <;>
      simp [show (-1 : ℝ) ≠ 1 by norm_num, simpleAction, Matrix.vecHead,
        Matrix.vecTail, Pi.single_apply, CharTwo.neg_eq, sub_eq_add_neg, Fin.ext_iff]

private theorem rootAction_conjugation_2 (r : Fin 24) (a : k) (z : HyperbolicSpace k 4) :
    simpleAction k 2 (rootAction k (rootAt r) a (simpleAction k 2 z)) =
      rootAction k (rootAt (reflectionIndex 2 r)) a z := by
  fin_cases r
  · exact rootAction_conjugation_2_01 k 0 a z
  · exact rootAction_conjugation_2_01 k 1 a z
  · exact rootAction_conjugation_2_01 k 2 a z
  · exact rootAction_conjugation_2_01 k 3 a z
  · exact rootAction_conjugation_2_02 k 0 a z
  · exact rootAction_conjugation_2_02 k 1 a z
  · exact rootAction_conjugation_2_02 k 2 a z
  · exact rootAction_conjugation_2_02 k 3 a z
  · exact rootAction_conjugation_2_03 k 0 a z
  · exact rootAction_conjugation_2_03 k 1 a z
  · exact rootAction_conjugation_2_03 k 2 a z
  · exact rootAction_conjugation_2_03 k 3 a z
  · exact rootAction_conjugation_2_12 k 0 a z
  · exact rootAction_conjugation_2_12 k 1 a z
  · exact rootAction_conjugation_2_12 k 2 a z
  · exact rootAction_conjugation_2_12 k 3 a z
  · exact rootAction_conjugation_2_13 k 0 a z
  · exact rootAction_conjugation_2_13 k 1 a z
  · exact rootAction_conjugation_2_13 k 2 a z
  · exact rootAction_conjugation_2_13 k 3 a z
  · exact rootAction_conjugation_2_23 k 0 a z
  · exact rootAction_conjugation_2_23 k 1 a z
  · exact rootAction_conjugation_2_23 k 2 a z
  · exact rootAction_conjugation_2_23 k 3 a z

private theorem rootAction_conjugation_3_01 (r : Fin 4) (a : k)
    (z : HyperbolicSpace k 4) :
    simpleAction k 3 (rootAction k (rootAt ⟨r.val + 0, by omega⟩) a (simpleAction k 3 z)) =
      rootAction k (rootAt (reflectionIndex 3 ⟨r.val + 0, by omega⟩)) a z := by
  fin_cases r
  all_goals
    norm_num [rootAt, reflectionIndex, rootAction]
    apply Prod.ext <;> funext p <;> fin_cases p <;>
      simp [show (-1 : ℝ) ≠ 1 by norm_num, simpleAction, Matrix.vecHead,
        Matrix.vecTail, Pi.single_apply, CharTwo.neg_eq, sub_eq_add_neg, Fin.ext_iff]

private theorem rootAction_conjugation_3_02 (r : Fin 4) (a : k)
    (z : HyperbolicSpace k 4) :
    simpleAction k 3 (rootAction k (rootAt ⟨r.val + 4, by omega⟩) a (simpleAction k 3 z)) =
      rootAction k (rootAt (reflectionIndex 3 ⟨r.val + 4, by omega⟩)) a z := by
  fin_cases r
  all_goals
    norm_num [rootAt, reflectionIndex, rootAction]
    apply Prod.ext <;> funext p <;> fin_cases p <;>
      simp [show (-1 : ℝ) ≠ 1 by norm_num, simpleAction, Matrix.vecHead,
        Matrix.vecTail, Pi.single_apply, CharTwo.neg_eq, sub_eq_add_neg, Fin.ext_iff]

private theorem rootAction_conjugation_3_03 (r : Fin 4) (a : k)
    (z : HyperbolicSpace k 4) :
    simpleAction k 3 (rootAction k (rootAt ⟨r.val + 8, by omega⟩) a (simpleAction k 3 z)) =
      rootAction k (rootAt (reflectionIndex 3 ⟨r.val + 8, by omega⟩)) a z := by
  fin_cases r
  all_goals
    norm_num [rootAt, reflectionIndex, rootAction]
    apply Prod.ext <;> funext p <;> fin_cases p <;>
      simp [show (-1 : ℝ) ≠ 1 by norm_num, simpleAction, Matrix.vecHead,
        Matrix.vecTail, Pi.single_apply, CharTwo.neg_eq, sub_eq_add_neg, Fin.ext_iff]

private theorem rootAction_conjugation_3_12 (r : Fin 4) (a : k)
    (z : HyperbolicSpace k 4) :
    simpleAction k 3 (rootAction k (rootAt ⟨r.val + 12, by omega⟩) a (simpleAction k 3 z)) =
      rootAction k (rootAt (reflectionIndex 3 ⟨r.val + 12, by omega⟩)) a z := by
  fin_cases r
  all_goals
    norm_num [rootAt, reflectionIndex, rootAction]
    apply Prod.ext <;> funext p <;> fin_cases p <;>
      simp [show (-1 : ℝ) ≠ 1 by norm_num, simpleAction, Matrix.vecHead,
        Matrix.vecTail, Pi.single_apply, CharTwo.neg_eq, sub_eq_add_neg, Fin.ext_iff]

private theorem rootAction_conjugation_3_13 (r : Fin 4) (a : k)
    (z : HyperbolicSpace k 4) :
    simpleAction k 3 (rootAction k (rootAt ⟨r.val + 16, by omega⟩) a (simpleAction k 3 z)) =
      rootAction k (rootAt (reflectionIndex 3 ⟨r.val + 16, by omega⟩)) a z := by
  fin_cases r
  all_goals
    norm_num [rootAt, reflectionIndex, rootAction]
    apply Prod.ext <;> funext p <;> fin_cases p <;>
      simp [show (-1 : ℝ) ≠ 1 by norm_num, simpleAction, Matrix.vecHead,
        Matrix.vecTail, Pi.single_apply, CharTwo.neg_eq, sub_eq_add_neg, Fin.ext_iff]

private theorem rootAction_conjugation_3_23 (r : Fin 4) (a : k)
    (z : HyperbolicSpace k 4) :
    simpleAction k 3 (rootAction k (rootAt ⟨r.val + 20, by omega⟩) a (simpleAction k 3 z)) =
      rootAction k (rootAt (reflectionIndex 3 ⟨r.val + 20, by omega⟩)) a z := by
  fin_cases r
  all_goals
    norm_num [rootAt, reflectionIndex, rootAction]
    apply Prod.ext <;> funext p <;> fin_cases p <;>
      simp [show (-1 : ℝ) ≠ 1 by norm_num, simpleAction, Matrix.vecHead,
        Matrix.vecTail, Pi.single_apply, CharTwo.neg_eq, sub_eq_add_neg, Fin.ext_iff]

private theorem rootAction_conjugation_3 (r : Fin 24) (a : k) (z : HyperbolicSpace k 4) :
    simpleAction k 3 (rootAction k (rootAt r) a (simpleAction k 3 z)) =
      rootAction k (rootAt (reflectionIndex 3 r)) a z := by
  fin_cases r
  · exact rootAction_conjugation_3_01 k 0 a z
  · exact rootAction_conjugation_3_01 k 1 a z
  · exact rootAction_conjugation_3_01 k 2 a z
  · exact rootAction_conjugation_3_01 k 3 a z
  · exact rootAction_conjugation_3_02 k 0 a z
  · exact rootAction_conjugation_3_02 k 1 a z
  · exact rootAction_conjugation_3_02 k 2 a z
  · exact rootAction_conjugation_3_02 k 3 a z
  · exact rootAction_conjugation_3_03 k 0 a z
  · exact rootAction_conjugation_3_03 k 1 a z
  · exact rootAction_conjugation_3_03 k 2 a z
  · exact rootAction_conjugation_3_03 k 3 a z
  · exact rootAction_conjugation_3_12 k 0 a z
  · exact rootAction_conjugation_3_12 k 1 a z
  · exact rootAction_conjugation_3_12 k 2 a z
  · exact rootAction_conjugation_3_12 k 3 a z
  · exact rootAction_conjugation_3_13 k 0 a z
  · exact rootAction_conjugation_3_13 k 1 a z
  · exact rootAction_conjugation_3_13 k 2 a z
  · exact rootAction_conjugation_3_13 k 3 a z
  · exact rootAction_conjugation_3_23 k 0 a z
  · exact rootAction_conjugation_3_23 k 1 a z
  · exact rootAction_conjugation_3_23 k 2 a z
  · exact rootAction_conjugation_3_23 k 3 a z

/-- The scalar action of each pinned normalizer realizes the checked reflection. -/
theorem rootAction_conjugation (i : Fin 4) (r : Fin 24) (a : k)
    (z : HyperbolicSpace k 4) :
    simpleAction k i (rootAction k (rootAt r) a (simpleAction k i z)) =
      rootAction k (rootAt (reflectionIndex i r)) a z := by
  fin_cases i
  · exact rootAction_conjugation_0 k r a z
  · exact rootAction_conjugation_1 k r a z
  · exact rootAction_conjugation_2 k r a z
  · exact rootAction_conjugation_3 k r a z

end Triality.SimplyConnected.Pinning.PointGeneration
