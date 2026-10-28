module

public import Theory.Representation.HigmanSims.LargeModels.TracePair.Descent.MatrixRelations.LongWords.Checks.LastTwo.R2.Batch00
public import Theory.Representation.HigmanSims.LargeModels.TracePair.Descent.MatrixRelations.LongWords.Checks.LastTwo.R2.Batch01
public import Theory.Representation.HigmanSims.LargeModels.TracePair.Descent.MatrixRelations.LongWords.Checks.LastTwo.R2.Batch02
public import Theory.Representation.HigmanSims.LargeModels.TracePair.Descent.MatrixRelations.LongWords.Checks.LastTwo.R2.Batch03
public import Theory.Representation.HigmanSims.LargeModels.TracePair.Descent.MatrixRelations.LongWords.Checks.LastTwo.R2.Batch04
public import Theory.Representation.HigmanSims.LargeModels.TracePair.Descent.MatrixRelations.LongWords.Checks.LastTwo.R2.Batch05
public import Theory.Representation.HigmanSims.LargeModels.TracePair.Descent.MatrixRelations.LongWords.Checks.LastTwo.R2.Batch06
public import Theory.Representation.HigmanSims.LargeModels.TracePair.Descent.MatrixRelations.LongWords.Checks.LastTwo.R2.Batch07
public import Theory.Representation.HigmanSims.LargeModels.TracePair.Descent.MatrixRelations.LongWords.Checks.LastTwo.R2.Batch08
public import Theory.Representation.HigmanSims.LargeModels.TracePair.Descent.MatrixRelations.LongWords.Checks.LastTwo.R2.Batch09
public import Theory.Representation.HigmanSims.LargeModels.TracePair.Descent.MatrixRelations.LongWords.Checks.LastTwo.R2.Batch10
public import Theory.Representation.HigmanSims.LargeModels.TracePair.Descent.MatrixRelations.LongWords.Checks.LastTwo.R2.Batch11
public import Theory.Representation.HigmanSims.LargeModels.TracePair.Descent.MatrixRelations.LongWords.Checks.LastTwo.R2.Batch12
public import Theory.Representation.HigmanSims.LargeModels.TracePair.Descent.MatrixRelations.LongWords.Checks.LastTwo.R2.Batch13

import Mathlib.Tactic.FinCases

/-!
# The five literal product gates for HS relator R2

Fourteen checked blocks cover every row of all five products, in source order:
(6,6) → 36, (11,16) → 37, (3,11) → 38, (36,37) → 39, (39,38) → 40.
Candidate 40 is the specified identity matrix. The checks use the unchanged
HSG1-f4r896aB0 matrices and two-plane encoding over Four; no earlier gate or
word interpretation is assumed. See `R2/source/README.md` and the exact
circuit in `LongWords/source/circuit.json`.
-/

public section
namespace Representation.HigmanSims.LargeModels.TracePair.Descent.MatrixRelations.LongWords
namespace R2

/-- All 896 rows of numerical gate 34, with no additional premises. -/
theorem gate34_product : ProductCheck 34 := by
  apply productCheck_of_batches
  intro b
  fin_cases b
  · exact Batch00.gate34
  · exact Batch01.gate34
  · exact Batch02.gate34
  · exact Batch03.gate34
  · exact Batch04.gate34
  · exact Batch05.gate34
  · exact Batch06.gate34
  · exact Batch07.gate34
  · exact Batch08.gate34
  · exact Batch09.gate34
  · exact Batch10.gate34
  · exact Batch11.gate34
  · exact Batch12.gate34
  · exact Batch13.gate34

/-- All 896 rows of numerical gate 35, with no additional premises. -/
theorem gate35_product : ProductCheck 35 := by
  apply productCheck_of_batches
  intro b
  fin_cases b
  · exact Batch00.gate35
  · exact Batch01.gate35
  · exact Batch02.gate35
  · exact Batch03.gate35
  · exact Batch04.gate35
  · exact Batch05.gate35
  · exact Batch06.gate35
  · exact Batch07.gate35
  · exact Batch08.gate35
  · exact Batch09.gate35
  · exact Batch10.gate35
  · exact Batch11.gate35
  · exact Batch12.gate35
  · exact Batch13.gate35

/-- All 896 rows of numerical gate 36, with no additional premises. -/
theorem gate36_product : ProductCheck 36 := by
  apply productCheck_of_batches
  intro b
  fin_cases b
  · exact Batch00.gate36
  · exact Batch01.gate36
  · exact Batch02.gate36
  · exact Batch03.gate36
  · exact Batch04.gate36
  · exact Batch05.gate36
  · exact Batch06.gate36
  · exact Batch07.gate36
  · exact Batch08.gate36
  · exact Batch09.gate36
  · exact Batch10.gate36
  · exact Batch11.gate36
  · exact Batch12.gate36
  · exact Batch13.gate36

/-- All 896 rows of numerical gate 37, with no additional premises. -/
theorem gate37_product : ProductCheck 37 := by
  apply productCheck_of_batches
  intro b
  fin_cases b
  · exact Batch00.gate37
  · exact Batch01.gate37
  · exact Batch02.gate37
  · exact Batch03.gate37
  · exact Batch04.gate37
  · exact Batch05.gate37
  · exact Batch06.gate37
  · exact Batch07.gate37
  · exact Batch08.gate37
  · exact Batch09.gate37
  · exact Batch10.gate37
  · exact Batch11.gate37
  · exact Batch12.gate37
  · exact Batch13.gate37

/-- All 896 rows of numerical gate 38, with no additional premises. -/
theorem gate38_product : ProductCheck 38 := by
  apply productCheck_of_batches
  intro b
  fin_cases b
  · exact Batch00.gate38
  · exact Batch01.gate38
  · exact Batch02.gate38
  · exact Batch03.gate38
  · exact Batch04.gate38
  · exact Batch05.gate38
  · exact Batch06.gate38
  · exact Batch07.gate38
  · exact Batch08.gate38
  · exact Batch09.gate38
  · exact Batch10.gate38
  · exact Batch11.gate38
  · exact Batch12.gate38
  · exact Batch13.gate38

end R2

/-- Every literal product in the R2 branch, including its identity endpoint. -/
theorem r2_products : ∀ i : Fin 46, 34 ≤ i.val → i.val < 39 → ProductCheck i := by
  intro i hlo hhi
  have h : i = 34 ∨ i = 35 ∨ i = 36 ∨ i = 37 ∨ i = 38 := by omega
  rcases h with rfl | rfl | rfl | rfl | rfl
  · exact R2.gate34_product
  · exact R2.gate35_product
  · exact R2.gate36_product
  · exact R2.gate37_product
  · exact R2.gate38_product

end Representation.HigmanSims.LargeModels.TracePair.Descent.MatrixRelations.LongWords
