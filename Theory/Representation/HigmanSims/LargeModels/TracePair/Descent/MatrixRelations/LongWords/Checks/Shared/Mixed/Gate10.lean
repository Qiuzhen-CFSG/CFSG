module

public import Theory.Representation.HigmanSims.LargeModels.TracePair.Descent.MatrixRelations.LongWords.Checks.Shared.Mixed.Gate10.Part00
public import Theory.Representation.HigmanSims.LargeModels.TracePair.Descent.MatrixRelations.LongWords.Checks.Shared.Mixed.Gate10.Part01
public import Theory.Representation.HigmanSims.LargeModels.TracePair.Descent.MatrixRelations.LongWords.Checks.Shared.Mixed.Gate10.Part02
public import Theory.Representation.HigmanSims.LargeModels.TracePair.Descent.MatrixRelations.LongWords.Checks.Shared.Mixed.Gate10.Part03

/-!
# The fixed mixed product at gate 10

Certificates for the literal HSG1-f4r896aB0 candidates. The generator
proposes witnesses only; all arithmetic equalities are checked by the kernel.
Source attribution and conventions: `TracePair/source/README.md`.
-/

@[expose] public section
namespace Representation.HigmanSims.LargeModels.TracePair.Descent.MatrixRelations.LongWords.Shared.Mixed.Gate10
open Representation.HigmanSims.LargeModels.TracePair.Certificates
open Representation.HigmanSims.LargeModels.TracePair.Descent.MatrixRelations.PowerChecks.LinearCertificates

/-- The product of literal candidates 9 and 7 is candidate 12. -/
theorem product_checked : ProductCheck 10 := by
  apply eval_product
  intro i
  have h : (i.val < 224) ∨ (224 ≤ i.val ∧ i.val < 448) ∨
      (448 ≤ i.val ∧ i.val < 672) ∨ (672 ≤ i.val) := by omega
  rcases h with h | h | h | h
  · exact part00 i.val (by omega) h
  · exact part01 i.val h.1 h.2
  · exact part02 i.val h.1 h.2
  · exact part03 i.val h (by omega)

end Representation.HigmanSims.LargeModels.TracePair.Descent.MatrixRelations.LongWords.Shared.Mixed.Gate10
