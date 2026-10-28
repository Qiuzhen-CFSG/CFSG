module

public import Theory.SpecificGroups.Suzuki.SchurEightCover.AtlasModel.MatrixComparison.Pair

/-!
# Checked words placing the ATLAS matrix pair in the native triple

Each displayed word from `source/matrix_words.json` is checked as a chain
of single matrix multiplications. No GAP calculation is trusted. Keeping
intermediate matrices explicit bounds kernel reduction independently of the
word length. These memberships are used by `NativeEmbedding.lean`.

Source context: Aschbacher–Smith I.1.1 and I.1.3(5), printed p.407;
see `source/README.md` for the numerical data and multiplication convention.
-/

@[expose] public section
namespace BenderSuzuki.MatrixGroups.SchurEightCover.AtlasModel.MatrixComparison

private def aStep1 : Mat := !![code 7, code 0, code 0, code 0;
     code 0, code 5, code 0, code 0;
     code 0, code 0, code 4, code 0;
     code 0, code 0, code 0, code 2]

private theorem aStep1_eq :
    ((torusV) : Mat) * ((torusV) : Mat) = aStep1 := by decide +kernel

private def aStep2 : Mat := !![code 0, code 0, code 0, code 7;
     code 0, code 0, code 5, code 0;
     code 0, code 4, code 0, code 0;
     code 2, code 0, code 0, code 0]

private theorem aStep2_eq :
    aStep1 * ((weyl) : Mat) = aStep2 := by decide +kernel

private def aStep3 : Mat := !![code 0, code 0, code 0, code 7;
     code 0, code 0, code 5, code 5;
     code 0, code 4, code 4, code 0;
     code 2, code 2, code 2, code 2]

private theorem aStep3_eq :
    aStep2 * ((rootOne⁻¹ : GL8) : Mat) = aStep3 := by decide +kernel

private def aStep4 : Mat := !![code 0, code 0, code 0, code 4;
     code 0, code 0, code 3, code 2;
     code 0, code 6, code 2, code 0;
     code 5, code 4, code 7, code 6]

private theorem aStep4_eq :
    aStep3 * ((torusV) : Mat) = aStep4 := by decide +kernel

private def aStep5 : Mat := !![code 4, code 0, code 0, code 0;
     code 2, code 3, code 0, code 0;
     code 0, code 2, code 6, code 0;
     code 6, code 7, code 4, code 5]

private theorem aStep5_eq :
    aStep4 * ((weyl) : Mat) = aStep5 := by decide +kernel

private def aStep6 : Mat := !![code 4, code 4, code 0, code 4;
     code 2, code 5, code 3, code 5;
     code 0, code 2, code 7, code 7;
     code 6, code 2, code 5, code 6]

private theorem aStep6_eq :
    aStep5 * ((rootOne) : Mat) = aStep6 := by decide +kernel

private def aStep7 : Mat := !![code 7, code 6, code 0, code 1;
     code 5, code 7, code 1, code 2;
     code 0, code 4, code 5, code 4;
     code 2, code 4, code 3, code 3]

private theorem aStep7_eq :
    aStep6 * ((torusV) : Mat) = aStep7 := by decide +kernel

private def aStep8 : Mat := !![code 3, code 1, code 0, code 5;
     code 1, code 2, code 6, code 6;
     code 0, code 6, code 3, code 1;
     code 5, code 6, code 1, code 7]

private theorem aStep8_eq :
    aStep7 * ((torusV) : Mat) = aStep8 := by decide +kernel

private def aStep9 : Mat := !![code 5, code 0, code 1, code 3;
     code 6, code 6, code 2, code 1;
     code 1, code 3, code 6, code 0;
     code 7, code 1, code 6, code 5]

private theorem aStep9_eq :
    aStep8 * ((weyl) : Mat) = aStep9 := by decide +kernel

theorem matrixA_word :
    torusV * torusV * weyl * (rootOne⁻¹) * torusV * weyl * rootOne * torusV * torusV * weyl = matrixA := by
  apply Units.ext
  change ((torusV) : Mat) * ((torusV) : Mat) * ((weyl) : Mat) * ((rootOne⁻¹ : GL8) : Mat) * ((torusV) : Mat) *
    ((weyl) : Mat) * ((rootOne) : Mat) * ((torusV) : Mat) * ((torusV) : Mat) * ((weyl) : Mat) = (matrixA :
    Mat)
  rw [aStep1_eq, aStep2_eq, aStep3_eq, aStep4_eq, aStep5_eq, aStep6_eq, aStep7_eq, aStep8_eq, aStep9_eq]
  rfl

theorem matrixA_mem_triple : matrixA ∈ tripleSubgroup := by
  rw [← matrixA_word]
  have hu : rootOne ∈ tripleSubgroup := Subgroup.subset_closure (by simp)
  have ht : torusV ∈ tripleSubgroup := Subgroup.subset_closure (by simp)
  have hw : weyl ∈ tripleSubgroup := Subgroup.subset_closure (by simp)
  exact (tripleSubgroup.mul_mem (tripleSubgroup.mul_mem (tripleSubgroup.mul_mem (tripleSubgroup.mul_mem
    (tripleSubgroup.mul_mem (tripleSubgroup.mul_mem (tripleSubgroup.mul_mem (tripleSubgroup.mul_mem
    (tripleSubgroup.mul_mem ht ht) hw) (tripleSubgroup.inv_mem hu)) ht) hw) hu) ht) ht) hw)

private def bStep1 : Mat := !![code 4, code 4, code 0, code 4;
     code 0, code 3, code 3, code 3;
     code 0, code 0, code 6, code 6;
     code 0, code 0, code 0, code 5]

private theorem bStep1_eq :
    ((torusV) : Mat) * ((rootOne) : Mat) = bStep1 := by decide +kernel

private def bStep2 : Mat := !![code 4, code 0, code 4, code 4;
     code 3, code 3, code 3, code 0;
     code 6, code 6, code 0, code 0;
     code 5, code 0, code 0, code 0]

private theorem bStep2_eq :
    bStep1 * ((weyl) : Mat) = bStep2 := by decide +kernel

private def bStep3 : Mat := !![code 4, code 4, code 4, code 4;
     code 3, code 0, code 0, code 3;
     code 6, code 0, code 6, code 0;
     code 5, code 5, code 0, code 5]

private theorem bStep3_eq :
    bStep2 * ((rootOne) : Mat) = bStep3 := by decide +kernel

private def bStep4 : Mat := !![code 4, code 4, code 4, code 4;
     code 3, code 0, code 0, code 3;
     code 0, code 6, code 0, code 6;
     code 5, code 0, code 5, code 5]

private theorem bStep4_eq :
    bStep3 * ((weyl) : Mat) = bStep4 := by decide +kernel

private def bStep5 : Mat := !![code 7, code 6, code 2, code 1;
     code 6, code 0, code 0, code 7;
     code 0, code 1, code 0, code 3;
     code 1, code 0, code 3, code 2]

private theorem bStep5_eq :
    bStep4 * ((torusV) : Mat) = bStep5 := by decide +kernel

private def bStep6 : Mat := !![code 7, code 2, code 7, code 1;
     code 6, code 6, code 0, code 2;
     code 0, code 1, code 1, code 7;
     code 1, code 1, code 3, code 6]

private theorem bStep6_eq :
    bStep5 * ((rootOne) : Mat) = bStep6 := by decide +kernel

private def bStep7 : Mat := !![code 3, code 4, code 5, code 5;
     code 2, code 1, code 0, code 6;
     code 0, code 3, code 6, code 4;
     code 4, code 3, code 1, code 3]

private theorem bStep7_eq :
    bStep6 * ((torusV) : Mat) = bStep7 := by decide +kernel

private def bStep8 : Mat := !![code 3, code 6, code 1, code 3;
     code 2, code 4, code 4, code 7;
     code 0, code 3, code 4, code 3;
     code 4, code 6, code 5, code 5]

private theorem bStep8_eq :
    bStep7 * ((rootOne⁻¹ : GL8) : Mat) = bStep8 := by decide +kernel

private def bStep9 : Mat := !![code 3, code 1, code 6, code 3;
     code 7, code 4, code 4, code 2;
     code 3, code 4, code 3, code 0;
     code 5, code 5, code 6, code 4]

private theorem bStep9_eq :
    bStep8 * ((weyl) : Mat) = bStep9 := by decide +kernel

theorem matrixB_word :
    torusV * rootOne * weyl * rootOne * weyl * torusV * rootOne * torusV * (rootOne⁻¹) * weyl = matrixB := by
  apply Units.ext
  change ((torusV) : Mat) * ((rootOne) : Mat) * ((weyl) : Mat) * ((rootOne) : Mat) * ((weyl) : Mat) *
    ((torusV) : Mat) * ((rootOne) : Mat) * ((torusV) : Mat) * ((rootOne⁻¹ : GL8) : Mat) * ((weyl) : Mat) =
    (matrixB : Mat)
  rw [bStep1_eq, bStep2_eq, bStep3_eq, bStep4_eq, bStep5_eq, bStep6_eq, bStep7_eq, bStep8_eq, bStep9_eq]
  rfl

theorem matrixB_mem_triple : matrixB ∈ tripleSubgroup := by
  rw [← matrixB_word]
  have hu : rootOne ∈ tripleSubgroup := Subgroup.subset_closure (by simp)
  have ht : torusV ∈ tripleSubgroup := Subgroup.subset_closure (by simp)
  have hw : weyl ∈ tripleSubgroup := Subgroup.subset_closure (by simp)
  exact (tripleSubgroup.mul_mem (tripleSubgroup.mul_mem (tripleSubgroup.mul_mem (tripleSubgroup.mul_mem
    (tripleSubgroup.mul_mem (tripleSubgroup.mul_mem (tripleSubgroup.mul_mem (tripleSubgroup.mul_mem
    (tripleSubgroup.mul_mem ht hu) hw) hu) hw) ht) hu) ht) (tripleSubgroup.inv_mem hu)) hw)

theorem pairSubgroup_le_triple : pairSubgroup ≤ tripleSubgroup := by
  apply (Subgroup.closure_le _).mpr
  intro g hg
  rcases hg with rfl | hg
  · exact matrixA_mem_triple
  · obtain rfl := Set.mem_singleton_iff.mp hg
    exact matrixB_mem_triple

end BenderSuzuki.MatrixGroups.SchurEightCover.AtlasModel.MatrixComparison
