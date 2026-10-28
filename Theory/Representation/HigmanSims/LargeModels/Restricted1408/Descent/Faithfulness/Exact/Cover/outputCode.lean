module

public import Theory.Representation.HigmanSims.LargeModels.Restricted1408.Descent.Faithfulness.Exact.Cover.outputCodeData00

/-! Centralizer-coset certificate for the thirteen ATLAS HS relators.
Untrusted data generated from the retained trace; all deduction checks use
Lean's kernel and the actual abstract relations. See `source/README.md`. -/

@[expose] public section
namespace Sporadic.LeechRelated.HS.AtlasPresentation.Exact.Cover
open Subgroup.CosetWordCertificate

def outputCode (i : Nat) : Nat :=
  unpack (branch 96 (branch 32 outputCodePage0 (branch 64 outputCodePage32 outputCodePage64)) (branch 128 outputCodePage96 (branch 160 outputCodePage128 outputCodePage160))) 19 i

end Sporadic.LeechRelated.HS.AtlasPresentation.Exact.Cover
