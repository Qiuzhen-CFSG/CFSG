module

public import Theory.Representation.HigmanSims.LargeModels.Restricted1408.Descent.Faithfulness.Exact.Cover.scanHeaderData00

/-! Centralizer-coset certificate for the thirteen ATLAS HS relators.
Untrusted data generated from the retained trace; all deduction checks use
Lean's kernel and the actual abstract relations. See `source/README.md`. -/

@[expose] public section
namespace Sporadic.LeechRelated.HS.AtlasPresentation.Exact.Cover
open Subgroup.CosetWordCertificate

def scanHeader (i : Nat) : Nat :=
  unpack (branch 128 (branch 64 (branch 32 scanHeaderPage0 scanHeaderPage32) (branch 96 scanHeaderPage64 scanHeaderPage96)) (branch 192 (branch 160 scanHeaderPage128 scanHeaderPage160) (branch 224 scanHeaderPage192 scanHeaderPage224))) 30 i

end Sporadic.LeechRelated.HS.AtlasPresentation.Exact.Cover
