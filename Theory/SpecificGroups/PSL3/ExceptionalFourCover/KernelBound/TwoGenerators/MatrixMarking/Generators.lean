module

public import Theory.SpecificGroups.PSL3.ExceptionalFourCover.KernelBound.TwoGenerators.MatrixMarking.Words

/-!
# Generation by the four-relator matrix marking

The six checked root words give the coefficients 1 and z on the directed
coordinate cycle. Root addition gives all of F₄; the elementary commutator
identity gives the other three roots. Elementary generation then proves that
A and B generate the full special linear group, without any order computation.

This supplies the generation part of the CHRR (2004), Table 2 matrix comparison.
The reused ATLAS elementary-generation API and its attribution are in
`Theory/AtlasPort/ExceptionalIsomorphisms/Elementary.lean`.
-/

@[expose] public section

namespace Matrix.PSL3.ExceptionalFourCover.TwoGeneratorPresentation.MatrixMarking
open Matrix.SpecialLinearGroup

private theorem field_cases : ∀ c : F, c = 0 ∨ c = 1 ∨ c = z ∨ c = z + 1 := by
  decide +kernel

/-- The six checked root words generate all of SL₃ over the concrete field. -/
theorem pair_generates : Subgroup.closure ({A, B} : Set SL) = ⊤ := by
  let K := Subgroup.closure ({A, B} : Set SL)
  have hA : A ∈ K := Subgroup.subset_closure (Set.mem_insert _ _)
  have hB : B ∈ K := Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)
  have hiA : A⁻¹ ∈ K := K.inv_mem hA
  have hiB : B⁻¹ ∈ K := K.inv_mem hB
  have h01one : Matrix.SpecialLinearGroup.transvection (show (0 : Fin 3) ≠ 1 by decide) (1 : F) ∈ K := by
    rw [← root01One_word]
    exact (K.mul_mem (K.mul_mem (K.mul_mem (K.mul_mem (K.mul_mem (K.mul_mem (K.mul_mem (K.mul_mem (K.mul_mem (K.mul_mem (K.mul_mem hA hA) hiB) hiA) hB) hiA) hB) hiA) hiB) hA) hB) hA)
  have h01z : Matrix.SpecialLinearGroup.transvection (show (0 : Fin 3) ≠ 1 by decide) z ∈ K := by
    rw [← root01Z_word]
    exact (K.mul_mem (K.mul_mem (K.mul_mem (K.mul_mem (K.mul_mem (K.mul_mem (K.mul_mem (K.mul_mem (K.mul_mem hA hiB) hA) hiB) hA) hiB) hiB) hiA) hB) hA)
  have h12one : Matrix.SpecialLinearGroup.transvection (show (1 : Fin 3) ≠ 2 by decide) (1 : F) ∈ K := by
    rw [← root12One_word]
    exact (K.mul_mem (K.mul_mem (K.mul_mem (K.mul_mem (K.mul_mem (K.mul_mem (K.mul_mem (K.mul_mem (K.mul_mem (K.mul_mem (K.mul_mem (K.mul_mem hA hA) hB) hiA) hiB) hA) hiB) hiB) hA) hB) hB) hA) hiB)
  have h12z : Matrix.SpecialLinearGroup.transvection (show (1 : Fin 3) ≠ 2 by decide) z ∈ K := by
    rw [← root12Z_word]
    exact (K.mul_mem (K.mul_mem (K.mul_mem (K.mul_mem (K.mul_mem (K.mul_mem (K.mul_mem (K.mul_mem (K.mul_mem (K.mul_mem (K.mul_mem hA hA) hiB) hiB) hA) hiB) hiA) hiA) hB) hB) hA) hiB)
  have h20one : Matrix.SpecialLinearGroup.transvection (show (2 : Fin 3) ≠ 0 by decide) (1 : F) ∈ K := by
    rw [← root20One_word]
    exact (K.mul_mem (K.mul_mem (K.mul_mem (K.mul_mem (K.mul_mem (K.mul_mem (K.mul_mem (K.mul_mem (K.mul_mem (K.mul_mem hB hB) hiA) hB) hA) hA) hB) hB) hA) hA) hB)
  have h20z : Matrix.SpecialLinearGroup.transvection (show (2 : Fin 3) ≠ 0 by decide) z ∈ K := by
    rw [← root20Z_word]
    exact (K.mul_mem (K.mul_mem (K.mul_mem (K.mul_mem (K.mul_mem (K.mul_mem (K.mul_mem (K.mul_mem (K.mul_mem (K.mul_mem (K.mul_mem hA hiB) hiA) hiA) hB) hiA) hiA) hiB) hA) hiB) hA) hB)
  have span (i j : Fin 3) (hij : i ≠ j)
      (h1 : Matrix.SpecialLinearGroup.transvection hij (1 : F) ∈ K)
      (hz : Matrix.SpecialLinearGroup.transvection hij z ∈ K) (c : F) :
      Matrix.SpecialLinearGroup.transvection hij c ∈ K := by
    rcases field_cases c with rfl | rfl | rfl | rfl
    · simpa only [transvection_coeff_zero] using K.one_mem
    · exact h1
    · exact hz
    · rw [transvection_add]
      exact K.mul_mem hz h1
  have h01 := span 0 1 (by decide) h01one h01z
  have h12 := span 1 2 (by decide) h12one h12z
  have h20 := span 2 0 (by decide) h20one h20z
  have h02 (c : F) : Matrix.SpecialLinearGroup.transvection (show (0 : Fin 3) ≠ 2 by decide) c ∈ K := by
    have h := K.commutator_le_self (Subgroup.commutator_mem_commutator (h01 c) (h12 1))
    simpa only [Atlas.elementary_commutator (i := (0 : Fin 3)) (j := 2) (k := 1)
      (by decide) (by decide) (by decide) c 1, mul_one] using h
  have h10 (c : F) : Matrix.SpecialLinearGroup.transvection (show (1 : Fin 3) ≠ 0 by decide) c ∈ K := by
    have h := K.commutator_le_self (Subgroup.commutator_mem_commutator (h12 c) (h20 1))
    simpa only [Atlas.elementary_commutator (i := (1 : Fin 3)) (j := 0) (k := 2)
      (by decide) (by decide) (by decide) c 1, mul_one] using h
  have h21 (c : F) : Matrix.SpecialLinearGroup.transvection (show (2 : Fin 3) ≠ 1 by decide) c ∈ K := by
    have h := K.commutator_le_self (Subgroup.commutator_mem_commutator (h20 c) (h01 1))
    simpa only [Atlas.elementary_commutator (i := (2 : Fin 3)) (j := 1) (k := 0)
      (by decide) (by decide) (by decide) c 1, mul_one] using h
  apply top_unique
  intro g _
  apply Atlas.sl_elementary_induction (fun g => g ∈ K) _ (fun _ _ => K.mul_mem) g
  intro i j hij c
  fin_cases i <;> fin_cases j <;>
    first | exact False.elim (hij rfl) | exact h01 c | exact h02 c |
      exact h10 c | exact h12 c | exact h20 c | exact h21 c

end Matrix.PSL3.ExceptionalFourCover.TwoGeneratorPresentation.MatrixMarking
