module

public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1242.OrbitBases.Data

/-!
# Realizing the certified orbit trees

Strong induction on each predecessor recovers a word in the original matrices.
Column recurrences prepend their letters; row recurrences append them. The
transpose comparison retains the literal untransposed ATLAS action.
Source: `../source/README.md`; James, J. Algebra 27 (1973), 57–111.
-/

@[expose] public section
namespace Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1242.OrbitBases
open Thompson.BinaryMatrix Matrix

/-- Earlier-predecessor column recurrences prepend the next generator. -/
theorem column_realizations (xs parents letters : List ℕ)
    (hseed : entry xs 0 = columnPacked)
    (hstep : ∀ i : Fin 1242, i.val ≠ 0 → entry parents i.val < i.val ∧
      (if entry letters i.val == 1 then Data1242.second else Data1242.first).mulVec
        (vector (entry xs (entry parents i.val))) = vector (entry xs i.val)) :
    Set.range (matrix (n := 1242) xs) ⊆ Set.range columnOrbit := by
  suffices main : ∀ i : Fin 1242, ∃ w, columnOrbit w = matrix xs i by
    rintro _ ⟨i, rfl⟩
    exact main i
  intro i
  induction i using WellFoundedLT.induction with
  | ind i ih =>
    by_cases hi : i.val = 0
    · refine ⟨[], ?_⟩
      change (1 : Mat).mulVec Density1242.column = vector (entry xs i.val)
      rw [one_mulVec, hi, hseed]
      rfl
    · obtain ⟨hp, hs⟩ := hstep i hi
      obtain ⟨w, hw⟩ := ih ⟨entry parents i.val, lt_trans hp i.isLt⟩ hp
      refine ⟨(entry letters i.val == 1) :: w, ?_⟩
      change ((if entry letters i.val == 1 then Data1242.second else Data1242.first) *
        wordValue Data1242.first Data1242.second w).mulVec column = _
      rw [← mulVec_mulVec]
      change (if entry letters i.val == 1 then Data1242.second else Data1242.first).mulVec
        (columnOrbit w) = _
      rw [hw]
      exact hs

/-- Earlier-predecessor row recurrences append the next generator. -/
theorem row_realizations (xs parents letters : List ℕ)
    (hseed : entry xs 0 = rowPacked)
    (hstep : ∀ i : Fin 1242, i.val ≠ 0 → entry parents i.val < i.val ∧
      vecMul (vector (entry xs (entry parents i.val)))
        (if entry letters i.val == 1 then Data1242.second else Data1242.first) =
        vector (entry xs i.val)) :
    Set.range (matrix (n := 1242) xs) ⊆ Set.range rowOrbit := by
  suffices main : ∀ i : Fin 1242, ∃ w, rowOrbit w = matrix xs i by
    rintro _ ⟨i, rfl⟩
    exact main i
  intro i
  induction i using WellFoundedLT.induction with
  | ind i ih =>
    by_cases hi : i.val = 0
    · refine ⟨[], ?_⟩
      change vecMul Density1242.row (1 : Mat) = vector (entry xs i.val)
      rw [vecMul_one, hi, hseed]
      rfl
    · obtain ⟨hp, hs⟩ := hstep i hi
      obtain ⟨w, hw⟩ := ih ⟨entry parents i.val, lt_trans hp i.isLt⟩ hp
      refine ⟨w ++ [entry letters i.val == 1], ?_⟩
      have ha : wordValue Data1242.first Data1242.second (w ++ [entry letters i.val == 1]) =
          wordValue Data1242.first Data1242.second w *
          (if entry letters i.val == 1 then Data1242.second else Data1242.first) := by
        simp [wordValue]
      rw [rowOrbit, ha, ← vecMul_vecMul]
      change vecMul (rowOrbit w) _ = _
      rw [hw]
      exact hs

theorem row_basis_in_orbit
    (hcheck : ∀ i : Fin 1242, rowStepCheck i.val = true)
    (hfirst : Data1242.firstRows.toList.length = 1242)
    (hsecond : Data1242.secondRows.toList.length = 1242)
    (hseed : entry rowVectors 0 = rowPacked) :
    Set.range (matrix (n := 1242) rowVectors) ⊆ Set.range rowOrbit := by
  apply row_realizations rowVectors rowParents rowLetters hseed
  intro i hi
  have hh := hcheck i
  simp only [rowStepCheck, Bool.or_eq_true, beq_iff_eq, hi, false_or,
    Bool.and_eq_true, decide_eq_true_eq] at hh
  refine ⟨hh.1, ?_⟩
  simp only [beq_iff_eq]
  have hlen : (if entry rowLetters i.val = 1 then Data1242.secondRows.toList
      else Data1242.firstRows.toList).length = 1242 := by
    split_ifs
    · exact hsecond
    · exact hfirst
  have he := (vector_packedRow _ hlen (entry rowVectors (entry rowParents i.val))).symm
  rw [hh.2] at he
  have hm : matrix (n := 1242) (if entry rowLetters i.val = 1 then
      Data1242.secondRows.toList else Data1242.firstRows.toList) =
      (if entry rowLetters i.val = 1 then Data1242.second else Data1242.first) := by
    split_ifs <;> exact matrix_array _
  rw [hm] at he
  exact he

theorem column_basis_in_orbit
    (hcheck : ∀ i : Fin 1242, columnStepCheck i.val = true)
    (hfirst : firstTranspose.length = 1242)
    (hsecond : secondTranspose.length = 1242)
    (hfirstT : matrix (n := 1242) firstTranspose = Data1242.first.transpose)
    (hsecondT : matrix (n := 1242) secondTranspose = Data1242.second.transpose)
    (hseed : entry columnVectors 0 = columnPacked) :
    Set.range (matrix (n := 1242) columnVectors) ⊆ Set.range columnOrbit := by
  apply column_realizations columnVectors columnParents columnLetters hseed
  intro i hi
  have hh := hcheck i
  simp only [columnStepCheck, Bool.or_eq_true, beq_iff_eq, hi, false_or,
    Bool.and_eq_true, decide_eq_true_eq] at hh
  refine ⟨hh.1, ?_⟩
  simp only [beq_iff_eq]
  have hlen : (if entry columnLetters i.val = 1 then secondTranspose
      else firstTranspose).length = 1242 := by
    split_ifs
    · exact hsecond
    · exact hfirst
  have he := (vector_packedRow _ hlen (entry columnVectors (entry columnParents i.val))).symm
  rw [hh.2] at he
  have hm : matrix (n := 1242) (if entry columnLetters i.val = 1 then
      secondTranspose else firstTranspose) =
      (if entry columnLetters i.val = 1 then Data1242.second else Data1242.first).transpose := by
    split_ifs
    · exact hsecondT
    · exact hfirstT
  rw [hm, vecMul_transpose] at he
  exact he

set_option maxRecDepth 8192 in
theorem firstRows_length : Data1242.firstRows.toList.length = 1242 := by decide +kernel

set_option maxRecDepth 8192 in
theorem secondRows_length : Data1242.secondRows.toList.length = 1242 := by decide +kernel

set_option maxRecDepth 8192 in
theorem firstTranspose_length : firstTranspose.length = 1242 := by decide +kernel

set_option maxRecDepth 8192 in
theorem secondTranspose_length : secondTranspose.length = 1242 := by decide +kernel

set_option maxRecDepth 8192 in
theorem columnVectors_length : columnVectors.length = 1242 := by decide +kernel

set_option maxRecDepth 8192 in
theorem rowVectors_length : rowVectors.length = 1242 := by decide +kernel

theorem columnVectors_seed : entry columnVectors 0 = columnPacked := by decide +kernel

theorem rowVectors_seed : entry rowVectors 0 = rowPacked := by decide +kernel

end Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1242.OrbitBases
