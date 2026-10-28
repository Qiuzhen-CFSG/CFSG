module

public import Theory.Representation.HigmanSims.LargeModels.Restricted1408.Descent.Faithfulness.Exact.Cover.opCode
public import Theory.Representation.HigmanSims.LargeModels.Restricted1408.Descent.Faithfulness.Exact.Cover.scanHeader
public import Theory.Representation.HigmanSims.LargeModels.Restricted1408.Descent.Faithfulness.Exact.Cover.scanLeft
public import Theory.Representation.HigmanSims.LargeModels.Restricted1408.Descent.Faithfulness.Exact.Cover.scanRight
public import Theory.GroupTheory.CosetWordCertificate.RelatorScan

/-! Centralizer-coset certificate for the thirteen ATLAS HS relators.
Untrusted data generated from the retained trace; all deduction checks use
Lean's kernel and the actual abstract relations. See `source/README.md`. -/

@[expose] public section
namespace Sporadic.LeechRelated.HS.AtlasPresentation.Exact.Cover
open Subgroup.CosetWordCertificate

def refs : Nat → Nat → List Nat
  | 0, _ => []
  | n+1, c => if c == 0 then [] else (c % 524288 - 1) :: refs n (c >>> 19)

def instructions (n : Nat) : Scan.Op Nat :=
  let c := opCode n
  let a := c / 8 % 524288
  let b := c / 4194304
  match c % 8 with
  | 0 => .basic (.refl a)
  | 1 => .basic (.defining a)
  | 2 => .basic (.subgroup (decode a))
  | 3 => .basic (.relator a b)
  | 4 => .basic (.reverse a)
  | 5 => .basic (.compose a b)
  | _ => .scan (scanHeader a / 4096) (scanHeader a % 4096)
      (refs 40 (scanLeft a)) (refs 40 (scanRight a))

end Sporadic.LeechRelated.HS.AtlasPresentation.Exact.Cover
