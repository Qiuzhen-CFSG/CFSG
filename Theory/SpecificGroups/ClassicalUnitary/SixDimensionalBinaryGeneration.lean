module

public import Theory.SpecificGroups.ClassicalUnitary.SixDimensionalBinaryGeneration.Reduction
public import Theory.SpecificGroups.ClassicalUnitary.SixDimensionalBinaryGeneration.FourSpace

/-!
# Generation of projective U₆(2) by isotropic transvections

For each special unitary matrix, two successive column operations in the
transvection subgroup fix the first two coordinate vectors. The remaining
matrix lies in the literal embedded SU₄. The explicit block generation proved
in `FourSpace` completes the reduction, and the existing surjection from SU₆
gives generation of the full projective image. Consequently the specified
transvection permutations generate the full action image on isotropic lines
with an additional fixed point.

This is the generation step needed for GLS3 Table 5.3t
(`refs/KGroup/GLS3/Chapter5(sec3-).tex`). It does not identify a Fischer section
or assume simplicity of the matrix group.
-/

@[expose] public section

open Matrix
open scoped MatrixGroups
namespace Theory.SpecificGroups.U6Two
open Generation

/-- The proved two-column reduction leaves only the embedded SU₄ generation input. -/
theorem transvectionSubgroup_eq_top_of_fourSpaceGeneration
    (hfour : Generation.FourSpaceGeneration) :
    transvectionSubgroup = ⊤ := by
  apply (Subgroup.eq_top_iff' _).mpr
  intro g
  obtain ⟨A, rfl⟩ := project_surjective g
  obtain ⟨B, hB, _, hBA⟩ := Generation.unitVectorReduction 0 (by decide) (A.val • basisVector 0)
    ((hermitianNorm_mulVec A _).trans (basisVector_norm 0)) (by simp)
  have hBA0 : (B * A).val • basisVector 0 = basisVector 0 := by
    simpa only [Subgroup.coe_mul, mul_smul] using hBA
  have hx0 : ((B * A).val • basisVector 1) 0 = 0 :=
    smul_basis_coordinate_eq_zero (B * A) 0 1 hBA0 (by decide)
  obtain ⟨C, hC, hCfix, hCBA⟩ := Generation.unitVectorReduction 1 (by decide) ((B * A).val • basisVector 1)
    ((hermitianNorm_mulVec (B * A) _).trans (basisVector_norm 1)) (by
      intro j hj
      have hj0 : j = 0 := by apply Fin.ext; omega
      simpa [hj0] using hx0)
  have hC0 : C.val • basisVector 0 = basisVector 0 := hCfix 0 (by decide)
  have hCBA0 : (C * (B * A)).val • basisVector 0 = basisVector 0 := by
    rw [Subgroup.coe_mul, mul_smul, hBA0, hC0]
  have hCBA1 : (C * (B * A)).val • basisVector 1 = basisVector 1 := by
    simpa only [Subgroup.coe_mul, mul_smul] using hCBA
  have hf := hfour (C * (B * A)) hCBA0 hCBA1
  have hBA_mem := (generatedSpecial.mul_mem_cancel_left hC).mp hf
  exact (generatedSpecial.mul_mem_cancel_left hB).mp hBA_mem

/-- The specified isotropic transvections generate the exact projective SU₆(GF(4)) model. -/
theorem transvectionSubgroup_eq_top : transvectionSubgroup = ⊤ :=
  transvectionSubgroup_eq_top_of_fourSpaceGeneration Generation.fourSpaceGeneration

/-- On isotropic lines with the fixed singleton, the transvection permutations
generate the full projective unitary action image. -/
theorem transvectionPermutationSubgroup_eq_range :
    transvectionPermutationSubgroup = isotropicActionWithSingleton.range :=
  transvectionPermutationSubgroup_eq_range_of_generation transvectionSubgroup_eq_top

end Theory.SpecificGroups.U6Two
