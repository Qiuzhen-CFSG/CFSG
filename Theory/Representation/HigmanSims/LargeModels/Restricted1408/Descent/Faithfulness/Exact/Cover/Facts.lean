module

public import Theory.Representation.HigmanSims.LargeModels.Restricted1408.Descent.Faithfulness.Exact.Cover.factCode

/-! Centralizer-coset certificate for the thirteen ATLAS HS relators.
Untrusted data generated from the retained trace; all deduction checks use
Lean's kernel and the actual abstract relations. See `source/README.md`. -/

@[expose] public section
namespace Sporadic.LeechRelated.HS.AtlasPresentation.Exact.Cover
open Subgroup.CosetWordCertificate

def facts (n : Nat) : FactData Nat :=
  let c := factCode n
  let a := c / 262144 % 16
  ⟨c % 262144, if a == 0 then [] else [decode (a-1)], c / 4194304⟩

end Sporadic.LeechRelated.HS.AtlasPresentation.Exact.Cover
