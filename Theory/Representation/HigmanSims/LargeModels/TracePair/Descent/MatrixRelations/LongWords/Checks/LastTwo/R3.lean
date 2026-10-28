module

public import Theory.Representation.HigmanSims.LargeModels.TracePair.Descent.MatrixRelations.LongWords.Checks.LastTwo.R3.Batch00
public import Theory.Representation.HigmanSims.LargeModels.TracePair.Descent.MatrixRelations.LongWords.Checks.LastTwo.R3.Batch01
public import Theory.Representation.HigmanSims.LargeModels.TracePair.Descent.MatrixRelations.LongWords.Checks.LastTwo.R3.Batch02
public import Theory.Representation.HigmanSims.LargeModels.TracePair.Descent.MatrixRelations.LongWords.Checks.LastTwo.R3.Batch03
public import Theory.Representation.HigmanSims.LargeModels.TracePair.Descent.MatrixRelations.LongWords.Checks.LastTwo.R3.Batch04
public import Theory.Representation.HigmanSims.LargeModels.TracePair.Descent.MatrixRelations.LongWords.Checks.LastTwo.R3.Batch05
public import Theory.Representation.HigmanSims.LargeModels.TracePair.Descent.MatrixRelations.LongWords.Checks.LastTwo.R3.Batch06
public import Theory.Representation.HigmanSims.LargeModels.TracePair.Descent.MatrixRelations.LongWords.Checks.LastTwo.R3.Batch07
public import Theory.Representation.HigmanSims.LargeModels.TracePair.Descent.MatrixRelations.LongWords.Checks.LastTwo.R3.Batch08
public import Theory.Representation.HigmanSims.LargeModels.TracePair.Descent.MatrixRelations.LongWords.Checks.LastTwo.R3.Batch09
public import Theory.Representation.HigmanSims.LargeModels.TracePair.Descent.MatrixRelations.LongWords.Checks.LastTwo.R3.Batch10
public import Theory.Representation.HigmanSims.LargeModels.TracePair.Descent.MatrixRelations.LongWords.Checks.LastTwo.R3.Batch11
public import Theory.Representation.HigmanSims.LargeModels.TracePair.Descent.MatrixRelations.LongWords.Checks.LastTwo.R3.Batch12
public import Theory.Representation.HigmanSims.LargeModels.TracePair.Descent.MatrixRelations.LongWords.Checks.LastTwo.R3.Batch13

import Mathlib.Tactic.FinCases

/-!
# The seven literal product gates for HS relator R3

Fourteen checked blocks cover all 896 rows of every ordered product:
(6,5) → 41, (5,9) → 42, (5,1) → 43, (17,3) → 44,
(41,42) → 45, (43,44) → 46, and (45,46) → 47.
Candidate 47 is the identity. The unchanged HSG1-f4r896aB0 matrices and
Four encoding are preserved. Only generic arithmetic is reused from R2;
no R2 product or earlier word interpretation is a hypothesis. See
`R3/source/README.md` and `LongWords/source/circuit.json`.
-/

public section
namespace Representation.HigmanSims.LargeModels.TracePair.Descent.MatrixRelations.LongWords
namespace R3
open R2

/-- All 896 rows of numerical gate 39, with no additional premises. -/
theorem gate39_product : ProductCheck 39 := by
  apply productCheck_of_batches
  intro b
  fin_cases b
  · exact Batch00.gate39
  · exact Batch01.gate39
  · exact Batch02.gate39
  · exact Batch03.gate39
  · exact Batch04.gate39
  · exact Batch05.gate39
  · exact Batch06.gate39
  · exact Batch07.gate39
  · exact Batch08.gate39
  · exact Batch09.gate39
  · exact Batch10.gate39
  · exact Batch11.gate39
  · exact Batch12.gate39
  · exact Batch13.gate39

/-- All 896 rows of numerical gate 40, with no additional premises. -/
theorem gate40_product : ProductCheck 40 := by
  apply productCheck_of_batches
  intro b
  fin_cases b
  · exact Batch00.gate40
  · exact Batch01.gate40
  · exact Batch02.gate40
  · exact Batch03.gate40
  · exact Batch04.gate40
  · exact Batch05.gate40
  · exact Batch06.gate40
  · exact Batch07.gate40
  · exact Batch08.gate40
  · exact Batch09.gate40
  · exact Batch10.gate40
  · exact Batch11.gate40
  · exact Batch12.gate40
  · exact Batch13.gate40

/-- All 896 rows of numerical gate 41, with no additional premises. -/
theorem gate41_product : ProductCheck 41 := by
  apply productCheck_of_batches
  intro b
  fin_cases b
  · exact Batch00.gate41
  · exact Batch01.gate41
  · exact Batch02.gate41
  · exact Batch03.gate41
  · exact Batch04.gate41
  · exact Batch05.gate41
  · exact Batch06.gate41
  · exact Batch07.gate41
  · exact Batch08.gate41
  · exact Batch09.gate41
  · exact Batch10.gate41
  · exact Batch11.gate41
  · exact Batch12.gate41
  · exact Batch13.gate41

/-- All 896 rows of numerical gate 42, with no additional premises. -/
theorem gate42_product : ProductCheck 42 := by
  apply productCheck_of_batches
  intro b
  fin_cases b
  · exact Batch00.gate42
  · exact Batch01.gate42
  · exact Batch02.gate42
  · exact Batch03.gate42
  · exact Batch04.gate42
  · exact Batch05.gate42
  · exact Batch06.gate42
  · exact Batch07.gate42
  · exact Batch08.gate42
  · exact Batch09.gate42
  · exact Batch10.gate42
  · exact Batch11.gate42
  · exact Batch12.gate42
  · exact Batch13.gate42

/-- All 896 rows of numerical gate 43, with no additional premises. -/
theorem gate43_product : ProductCheck 43 := by
  apply productCheck_of_batches
  intro b
  fin_cases b
  · exact Batch00.gate43
  · exact Batch01.gate43
  · exact Batch02.gate43
  · exact Batch03.gate43
  · exact Batch04.gate43
  · exact Batch05.gate43
  · exact Batch06.gate43
  · exact Batch07.gate43
  · exact Batch08.gate43
  · exact Batch09.gate43
  · exact Batch10.gate43
  · exact Batch11.gate43
  · exact Batch12.gate43
  · exact Batch13.gate43

/-- All 896 rows of numerical gate 44, with no additional premises. -/
theorem gate44_product : ProductCheck 44 := by
  apply productCheck_of_batches
  intro b
  fin_cases b
  · exact Batch00.gate44
  · exact Batch01.gate44
  · exact Batch02.gate44
  · exact Batch03.gate44
  · exact Batch04.gate44
  · exact Batch05.gate44
  · exact Batch06.gate44
  · exact Batch07.gate44
  · exact Batch08.gate44
  · exact Batch09.gate44
  · exact Batch10.gate44
  · exact Batch11.gate44
  · exact Batch12.gate44
  · exact Batch13.gate44

/-- All 896 rows of numerical gate 45, with no additional premises. -/
theorem gate45_product : ProductCheck 45 := by
  apply productCheck_of_batches
  intro b
  fin_cases b
  · exact Batch00.gate45
  · exact Batch01.gate45
  · exact Batch02.gate45
  · exact Batch03.gate45
  · exact Batch04.gate45
  · exact Batch05.gate45
  · exact Batch06.gate45
  · exact Batch07.gate45
  · exact Batch08.gate45
  · exact Batch09.gate45
  · exact Batch10.gate45
  · exact Batch11.gate45
  · exact Batch12.gate45
  · exact Batch13.gate45

/-- The closing product is the actual identity matrix. -/
theorem gate45_identity : candidate 45 * candidate 46 = 1 :=
  gate45_product.trans identityRows_eval

end R3

/-- Every literal product in R3, including every row of its identity endpoint. -/
theorem r3_products : ∀ i : Fin 46, 39 ≤ i.val → ProductCheck i := by
  intro i hi
  have h : i = 39 ∨ i = 40 ∨ i = 41 ∨ i = 42 ∨ i = 43 ∨ i = 44 ∨ i = 45 := by omega
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact R3.gate39_product
  · exact R3.gate40_product
  · exact R3.gate41_product
  · exact R3.gate42_product
  · exact R3.gate43_product
  · exact R3.gate44_product
  · exact R3.gate45_product

end Representation.HigmanSims.LargeModels.TracePair.Descent.MatrixRelations.LongWords
