module

public import Theory.SpecificGroups.Janko3.RecognitionPresentation.OrderBound.M1Cover.factCode

/-! Kernel-checked coset certificate for ATLAS J3G1-P1, literal subgroup M₁.
Generated from `source/compact.json` by `source/generate.py`.
The data are untrusted; `Scan.chunk_sound` supplies actual subgroup witnesses. -/

@[expose] public section
namespace Sporadic.Janko3.RecognitionPresentation.OrderBound.M1Certificate
open Subgroup.CosetWordCertificate

def facts (n : Nat) : FactData (Fin 3) :=
  let c := factCode n
  let a := c / 262144 % 8
  ⟨c % 262144, if a == 0 then [] else [decode (a-1)], c / 2097152⟩

end Sporadic.Janko3.RecognitionPresentation.OrderBound.M1Certificate
