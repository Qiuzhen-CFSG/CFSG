module

public import Theory.Representation.HigmanSims.LargeModels.TracePair.Descent.MatrixRelations.LongWords.Checks.Shared.Mixed.Gate04
public import Theory.Representation.HigmanSims.LargeModels.TracePair.Descent.MatrixRelations.LongWords.Checks.Shared.Mixed.Gate07
public import Theory.Representation.HigmanSims.LargeModels.TracePair.Descent.MatrixRelations.LongWords.Checks.Shared.Mixed.Gate08
public import Theory.Representation.HigmanSims.LargeModels.TracePair.Descent.MatrixRelations.LongWords.Checks.Shared.Mixed.Gate10
public import Theory.Representation.HigmanSims.LargeModels.TracePair.Descent.MatrixRelations.LongWords.Checks.Shared.Mixed.Gate16

/-!
# The five mixed shared HS products

Certificates for the literal HSG1-f4r896aB0 candidates. The generator
proposes witnesses only; all arithmetic equalities are checked by the kernel.
Source attribution and conventions: `TracePair/source/README.md`.
-/

@[expose] public section
namespace Representation.HigmanSims.LargeModels.TracePair.Descent.MatrixRelations.LongWords
open Representation.HigmanSims.LargeModels.TracePair.Certificates
open Representation.HigmanSims.LargeModels.TracePair.Descent.MatrixRelations.PowerChecks.LinearCertificates

/-- Discharge the mixed family of fixed matrix products, with no earlier-gate
or representation assumptions. Candidate 7's coordinate certificates are shared
between gates 8 and 10. -/
theorem shared_mixed_products : ∀ i : Fin 46,
    (i = 4 ∨ i = 7 ∨ i = 8 ∨ i = 10 ∨ i = 16) → ProductCheck i := by
  intro i hi
  rcases hi with rfl | rfl | rfl | rfl | rfl
  · exact Shared.Mixed.Gate04.product_checked
  · exact Shared.Mixed.Gate07.product_checked
  · exact Shared.Mixed.Gate08.product_checked
  · exact Shared.Mixed.Gate10.product_checked
  · exact Shared.Mixed.Gate16.product_checked

end Representation.HigmanSims.LargeModels.TracePair.Descent.MatrixRelations.LongWords
