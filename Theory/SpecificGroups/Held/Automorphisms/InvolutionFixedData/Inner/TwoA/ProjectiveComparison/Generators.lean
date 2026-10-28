module

public import Theory.SpecificGroups.Held.Automorphisms.InvolutionFixedData.Inner.TwoA.ProjectiveComparison.MatrixSteps

/-!
# Generation by the two projective comparison matrices

The short checked words give a coordinate cycle and x₀₁(1), x₀₁(z).
Root addition gives x₀₁(c) for every field element. Conjugation by the cycle
gives the other two oriented root groups, and the elementary commutator
identity gives the three opposite root groups. Elementary generation then
proves generation of SL, hence of its actual central quotient PSL.

This uses the licensed ATLAS elementary-generation API with its original
attribution in `Theory/AtlasPort/ExceptionalIsomorphisms/Elementary.lean`.
It establishes the matrix side of the GLS3 Table 5.3p action comparison.
-/

@[expose] public section

namespace Held.InvolutionFixedData.TwoA.ProjectiveComparison
open Matrix.SpecialLinearGroup

private theorem field_cases : ∀ c : F, c = 0 ∨ c = 1 ∨ c = z ∨ c = z + 1 := by
  decide +kernel

private theorem cycle_root01 : ∀ c : F,
    cycle * transvection (show (0 : Fin 3) ≠ 1 by decide) c * cycle⁻¹ =
      transvection (show (1 : Fin 3) ≠ 2 by decide) c := by
  decide +kernel

private theorem cycle_root12 : ∀ c : F,
    cycle * transvection (show (1 : Fin 3) ≠ 2 by decide) c * cycle⁻¹ =
      transvection (show (2 : Fin 3) ≠ 0 by decide) c := by
  decide +kernel

/-- The two explicit matrix lifts generate the full special linear group. -/
theorem matrix_pair_generates : Subgroup.closure ({matrixA, matrixB} : Set SL) = ⊤ := by
  let K := Subgroup.closure ({matrixA, matrixB} : Set SL)
  have hA : matrixA ∈ K := Subgroup.subset_closure (Set.mem_insert _ _)
  have hB : matrixB ∈ K := Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)
  have hcycle : cycle ∈ K := cycle_mem K hA hB
  have h01 (c : F) : transvection (show (0 : Fin 3) ≠ 1 by decide) c ∈ K := by
    rcases field_cases c with rfl | rfl | rfl | rfl
    · simpa only [transvection_coeff_zero] using K.one_mem
    · exact rootOne_mem K hA hB
    · exact rootZ_mem K hA hB
    · rw [transvection_add]
      exact K.mul_mem (rootZ_mem K hA hB) (rootOne_mem K hA hB)
  have h12 (c : F) : transvection (show (1 : Fin 3) ≠ 2 by decide) c ∈ K := by
    rw [← cycle_root01]
    exact K.mul_mem (K.mul_mem hcycle (h01 c)) (K.inv_mem hcycle)
  have h20 (c : F) : transvection (show (2 : Fin 3) ≠ 0 by decide) c ∈ K := by
    rw [← cycle_root12]
    exact K.mul_mem (K.mul_mem hcycle (h12 c)) (K.inv_mem hcycle)
  have h02 (c : F) : transvection (show (0 : Fin 3) ≠ 2 by decide) c ∈ K := by
    have h := K.commutator_le_self (Subgroup.commutator_mem_commutator (h01 c) (h12 1))
    simpa only [Atlas.elementary_commutator (i := (0 : Fin 3)) (j := 2) (k := 1)
      (by decide) (by decide) (by decide) c 1, mul_one]
      using h
  have h10 (c : F) : transvection (show (1 : Fin 3) ≠ 0 by decide) c ∈ K := by
    have h := K.commutator_le_self (Subgroup.commutator_mem_commutator (h12 c) (h20 1))
    simpa only [Atlas.elementary_commutator (i := (1 : Fin 3)) (j := 0) (k := 2)
      (by decide) (by decide) (by decide) c 1, mul_one]
      using h
  have h21 (c : F) : transvection (show (2 : Fin 3) ≠ 1 by decide) c ∈ K := by
    have h := K.commutator_le_self (Subgroup.commutator_mem_commutator (h20 c) (h01 1))
    simpa only [Atlas.elementary_commutator (i := (2 : Fin 3)) (j := 1) (k := 0)
      (by decide) (by decide) (by decide) c 1, mul_one]
      using h
  apply top_unique
  intro g _
  apply Atlas.sl_elementary_induction (fun g => g ∈ K) _ (fun _ _ => K.mul_mem) g
  intro i j hij c
  fin_cases i <;> fin_cases j <;>
    first | exact False.elim (hij rfl) | exact h01 c | exact h02 c |
      exact h10 c | exact h12 c | exact h20 c | exact h21 c

/-- Quotienting the actual generated matrices gives generation of matrix PSL. -/
theorem projective_pair_generates :
    Subgroup.closure ({projectiveA, projectiveB} : Set PSL) = ⊤ := by
  have h := congrArg
    (Subgroup.map (QuotientGroup.mk' (Subgroup.center SL))) matrix_pair_generates
  rw [MonoidHom.map_closure, Set.image_insert_eq, Set.image_singleton,
    Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _)] at h
  exact h
end Held.InvolutionFixedData.TwoA.ProjectiveComparison
