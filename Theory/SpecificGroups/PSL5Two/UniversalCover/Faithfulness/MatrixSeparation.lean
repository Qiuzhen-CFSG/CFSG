module

public import Theory.SpecificGroups.PSL5Two.UniversalCover.Faithfulness.Setup
public import Mathlib.LinearAlgebra.Matrix.Permutation

/-!
# Separation of the upper and Weyl matrix images

The published matrix map takes upper-root words to upper-triangular matrices
and the three-letter Weyl words to actual coordinate permutation matrices.
These image subgroups intersect trivially: upper triangularity forces
`i ≤ σ(i)` for every coordinate, and equality of the sums forces `σ = 1`.

The argument does not assume either restricted map is injective. Together
with their separate faithfulness proofs and a Bruhat covering, it detects
the whole kernel. This is the matrix separation step of the type A₄
presentation argument underlying GLS98 §6.1 and Aschbacher–Smith I.1.3.
-/

@[expose] public section

namespace Theory.SpecificGroups.PSL5Two.UniversalCover.Faithfulness
open Matrix.SpecialLinearGroup

theorem matrixMap_weylWord (i j : Fin 5) (hij : i ≠ j) :
    (matrixMap (weylWord generator i j hij) : Matrix (Fin 5) (Fin 5) (ZMod 2)) =
      (Equiv.swap i j).permMatrix (ZMod 2) := by
  simp only [weylWord, map_mul, matrixMap_generator, coe_mul, matrixRoot,
    root, transvection_coe]
  change Matrix.transvection i j 1 * Matrix.transvection j i 1 *
    Matrix.transvection i j 1 = _
  rw [Matrix.mul_assoc]
  apply Matrix.ext
  intro k l
  by_cases hki : k = i
  · subst k
    simp only [Matrix.transvection_mul_apply_same, one_mul,
      Matrix.transvection_mul_apply_of_ne j i i l hij]
    by_cases hli : l = i <;> by_cases hlj : l = j
    all_goals
      simp_all [Matrix.transvection, Matrix.one_apply,
        Equiv.Perm.permMatrix, PEquiv.toMatrix_apply, eq_comm]
    all_goals exact (by decide : (0 : ZMod 2) = 2)
  by_cases hkj : k = j
  · subst k
    simp only [Matrix.transvection_mul_apply_of_ne i j j l (Ne.symm hij),
      Matrix.transvection_mul_apply_same, one_mul]
    by_cases hli : l = i <;> by_cases hlj : l = j
    all_goals
      simp_all [Matrix.transvection, Matrix.one_apply,
        Equiv.Perm.permMatrix, PEquiv.toMatrix_apply, eq_comm]
    all_goals exact (by decide : (0 : ZMod 2) = 2)
  simp only [Matrix.transvection_mul_apply_of_ne i j k l hki,
    Matrix.transvection_mul_apply_of_ne j i k l hkj]
  simp_all [Matrix.transvection, Matrix.one_apply,
    Equiv.Perm.permMatrix, PEquiv.toMatrix_apply,
    Equiv.swap_apply_of_ne_of_ne hki hkj, eq_comm]


theorem matrixMap_upper {u : SteinbergGroup} (hu : u ∈ upperSubgroup) :
    (matrixMap u : Matrix (Fin 5) (Fin 5) (ZMod 2)).IsUpperTriangular := by
  have hroot {r : Root} (hr : r ∈ positiveRoots) :
      (matrixMap (generator r) : Matrix (Fin 5) (Fin 5) (ZMod 2)).IsUpperTriangular := by
    rw [matrixMap_generator]
    exact Matrix.blockTriangular_transvection (b := id) (le_of_lt hr) 1
  induction hu using Subgroup.closure_induction_right with
  | one => simpa only [map_one, coe_one] using
      (Matrix.blockTriangular_one (R := ZMod 2) (b := id) (m := Fin 5))
  | mul_right z _ y hy ih =>
    obtain ⟨r, hr, rfl⟩ := hy
    simpa only [map_mul, coe_mul] using ih.mul (hroot hr)
  | mul_inv_cancel z _ y hy ih =>
    obtain ⟨r, hr, rfl⟩ := hy
    rw [generator_relations.inv]
    simpa only [map_mul, coe_mul] using ih.mul (hroot hr)

theorem matrixMap_weyl {w : SteinbergGroup} (hw : w ∈ weylSubgroup) :
    ∃ σ : Equiv.Perm (Fin 5),
      (matrixMap w : Matrix (Fin 5) (Fin 5) (ZMod 2)) = σ.permMatrix (ZMod 2) := by
  have step (z : SteinbergGroup) (r : Root)
      (hz : ∃ σ : Equiv.Perm (Fin 5),
        (matrixMap z : Matrix (Fin 5) (Fin 5) (ZMod 2)) = σ.permMatrix (ZMod 2)) :
      ∃ σ : Equiv.Perm (Fin 5),
        (matrixMap (z * weylGenerator r) : Matrix (Fin 5) (Fin 5) (ZMod 2)) =
          σ.permMatrix (ZMod 2) := by
    obtain ⟨σ, hσ⟩ := hz
    refine ⟨Equiv.swap r.val.1 r.val.2 * σ, ?_⟩
    rw [map_mul, coe_mul, hσ, Matrix.permMatrix_mul]
    exact congrArg (fun M => σ.permMatrix (ZMod 2) * M) (matrixMap_weylWord _ _ _)
  induction hw using Subgroup.closure_induction_right with
  | one => exact ⟨1, by simp⟩
  | mul_right z _ y hy ih =>
    obtain ⟨r, rfl⟩ := hy
    exact step z r ih
  | mul_inv_cancel z _ y hy ih =>
    obtain ⟨r, rfl⟩ := hy
    rw [weylGenerator_inv]
    exact step z r ih

private theorem perm_eq_one_of_upper (σ : Equiv.Perm (Fin 5))
    (hσ : (σ.permMatrix (ZMod 2)).IsUpperTriangular) : σ = 1 := by
  have hle (i : Fin 5) : i.val ≤ (σ i).val := by
    by_contra! hi
    have hz := hσ (i := i) (j := σ i) hi
    simp [Equiv.Perm.permMatrix, PEquiv.toMatrix_apply] at hz
  have hs : (∑ i : Fin 5, i.val) = ∑ i : Fin 5, (σ i).val :=
    (Equiv.sum_comp σ Fin.val).symm
  have he := (Finset.sum_eq_sum_iff_of_le (fun i (_ : i ∈ (Finset.univ : Finset (Fin 5))) =>
    hle i)).mp hs
  apply Equiv.ext
  intro i
  exact Fin.ext (he i (Finset.mem_univ i)).symm

/-- A coordinate permutation which is also upper triangular is the identity. -/
theorem matrixMap_eq_one_of_upper_of_weyl {u w : SteinbergGroup}
    (hu : u ∈ upperSubgroup) (hw : w ∈ weylSubgroup) (huw : matrixMap u = matrixMap w) :
    matrixMap w = 1 := by
  obtain ⟨σ, hσ⟩ := matrixMap_weyl hw
  have htri : (σ.permMatrix (ZMod 2)).IsUpperTriangular := by
    rw [← hσ, ← huw]
    exact matrixMap_upper hu
  have he := perm_eq_one_of_upper σ htri
  apply Subtype.ext
  simpa only [he, Matrix.permMatrix_one, coe_one] using hσ
end Theory.SpecificGroups.PSL5Two.UniversalCover.Faithfulness
