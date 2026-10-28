module

public import Theory.Representation.HigmanSims.LargeModels.Restricted1408.Descent.Faithfulness.Exact.Cover.destCodeData00

/-! Centralizer-coset certificate for the thirteen ATLAS HS relators.
Untrusted data generated from the retained trace; all deduction checks use
Lean's kernel and the actual abstract relations. See `source/README.md`. -/

@[expose] public section
namespace Sporadic.LeechRelated.HS.AtlasPresentation.Exact.Cover
open Subgroup.CosetWordCertificate

def destCode (i : Nat) : Nat :=
  unpack (branch 96 (branch 32 destCodePage0 (branch 64 destCodePage32 destCodePage64)) (branch 128 destCodePage96 (branch 160 destCodePage128 destCodePage160))) 13 i

end Sporadic.LeechRelated.HS.AtlasPresentation.Exact.Cover
