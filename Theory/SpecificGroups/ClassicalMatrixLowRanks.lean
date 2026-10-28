module

public import Theory.SpecificGroups.ClassicalUnitary.ProjectiveLinearEmbedding
public import Mathlib.LinearAlgebra.SymplecticGroup

/-!
# Degenerate classical matrix groups

SL on at most one coordinate is trivial. The actual projective unitary
image embeds in PSL over its coefficient field, so the same conclusion holds
for every Hermitian form. The rank-zero symplectic space has a unique matrix.
Surjectivity passes these facts to the literal projective quotients.

These are the small-parameter exclusions needed to compare the unrestricted
Lie-family predicate in Aschbacher–Smith Hypothesis 13.3.1(2), printed p.884,
with the simple classical ranges of GLS3 Theorem 2.2.7.
-/

@[expose] public section
namespace ClassicalMatrixLowRanks
open BenderSuzuki.MatrixGroups

/-- PSL in dimension at most one is trivial. -/
theorem psl_subsingleton (F : Type*) [Field F] (n : ℕ) (hn : n ≤ 1) :
    Subsingleton (Matrix.ProjectiveSpecialLinearGroup (Fin n) F) := by
  have : Subsingleton (Fin n) := Fin.subsingleton_iff_le_one.mpr hn
  exact (QuotientGroup.mk'_surjective _).subsingleton

/-- The same triviality holds for every Hermitian form, without normalizing it. -/
theorem psu_subsingleton (F : Type*) [Field F] (n : ℕ) (hn : n ≤ 1) (J : HermitianForm n F) :
    Subsingleton (ProjectiveSpecialUnitaryMatrixGroup J) := by
  have : Subsingleton (Fin n) := Fin.subsingleton_iff_le_one.mpr hn
  have : Subsingleton (Matrix.ProjectiveSpecialLinearGroup (Fin n) F) :=
    (QuotientGroup.mk'_surjective _).subsingleton
  obtain ⟨i, hi⟩ := J.exists_injective_projectiveSpecialLinear
  exact hi.subsingleton

/-- The rank-zero symplectic group and its central quotient are trivial. -/
theorem psp_zero_subsingleton (F : Type*) [Field F] :
    Subsingleton ((Matrix.symplecticGroup (Fin 0) F) ⧸
      Subgroup.center (Matrix.symplecticGroup (Fin 0) F)) := by
  exact (QuotientGroup.mk'_surjective _).subsingleton


end ClassicalMatrixLowRanks
