module
public import CFSG.Quasithin.ChapterB.Section03.Offenders.Eight.Canonical.Hyperplanes.Forms
import Mathlib.Tactic.FinCases

/-!
# Three-generator tables for the degree-eight hyperplanes

For each nonzero binary form, pivot at its first nonzero coefficient. The
remaining three coordinate vectors, corrected by that pivot when necessary,
form a basis of the kernel. The sixteen-word table checks generation directly.
This keeps the subsequent fixed-vector counts to three permutation tests.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*,
Proposition B.3.2(5),(6), printed pp. 83–84.
-/

@[expose] public section
namespace CFSG.Quasithin.ChapterB.Offenders.Eight

/-- A binary basis for each nonzero form kernel, pivoting at its first nonzero coefficient. -/
def hyperplaneBasisIndices : Fin 16 → Fin 3 → Fin 16 :=
  ![![1, 2, 4],
    ![2, 4, 8],
    ![1, 4, 8],
    ![3, 4, 8],
    ![1, 2, 8],
    ![2, 5, 8],
    ![1, 6, 8],
    ![3, 5, 8],
    ![1, 2, 4],
    ![2, 4, 9],
    ![1, 4, 10],
    ![3, 4, 9],
    ![1, 2, 12],
    ![2, 5, 9],
    ![1, 6, 10],
    ![3, 5, 9]]

/-- Three generators suffice for each hyperplane. -/
def hyperplaneBasisGenerators (m : Fin 16) : Finset Perm :=
  {dWords (hyperplaneBasisIndices m 0), dWords (hyperplaneBasisIndices m 1),
    dWords (hyperplaneBasisIndices m 2)}

/-- The three listed generators span the entire binary kernel. -/
theorem hyperplaneKernel_closure_basis (m : Fin 16) (hm : m ≠ 0) :
    hyperplaneKernel m = Subgroup.closure (hyperplaneBasisGenerators m : Set Perm) := by
  have hmem : ∀ n : Fin 16, n ≠ 0 → ∀ i : Fin 3,
      hyperplaneForm n (hyperplaneCoeffs (hyperplaneBasisIndices n i)) = 0 := by
    decide +kernel
  have hspan : ∀ n : Fin 16, n ≠ 0 → ∀ j : Fin 16,
      hyperplaneForm n (hyperplaneCoeffs j) = 0 →
      ∃ k : Fin 8,
        cubeWords (dWords (hyperplaneBasisIndices n 0))
          (dWords (hyperplaneBasisIndices n 1)) (dWords (hyperplaneBasisIndices n 2)) 1
          ⟨k.val, by omega⟩ = dWords j := by decide +kernel
  apply le_antisymm
  · intro g hg
    obtain ⟨j, hj, rfl⟩ := (mem_hyperplaneKernel m g).mp hg
    obtain ⟨k, hk⟩ := hspan m hm j hj
    rw [← hk]
    have hgen (i : Fin 3) : dWords (hyperplaneBasisIndices m i) ∈
        Subgroup.closure (hyperplaneBasisGenerators m : Set Perm) := by
      apply Subgroup.subset_closure
      fin_cases i <;> simp [hyperplaneBasisGenerators]
    unfold cubeWords
    repeat' apply Subgroup.mul_mem
    all_goals split_ifs
    all_goals first | exact hgen 0 | exact hgen 1 | exact hgen 2 | exact Subgroup.one_mem _
  · apply (Subgroup.closure_le _).mpr
    intro g hg
    simp only [hyperplaneBasisGenerators, Finset.mem_coe, Finset.mem_insert,
      Finset.mem_singleton] at hg
    rcases hg with rfl | rfl | rfl
    all_goals apply (dWords_mem_hyperplaneKernel _ _).mpr
    · exact hmem m hm 0
    · exact hmem m hm 1
    · exact hmem m hm 2

end CFSG.Quasithin.ChapterB.Offenders.Eight
