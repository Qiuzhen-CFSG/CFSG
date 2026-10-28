module

public import Theory.Representation.HigmanSims.LargeModels.Restricted1408.Descent.Faithfulness.Exact.Core

/-! Centralizer-coset certificate for the thirteen ATLAS HS relators.
Untrusted data generated from the retained trace; all deduction checks use
Lean's kernel and the actual abstract relations. See `source/README.md`. -/

@[expose] public section
namespace Sporadic.LeechRelated.HS.AtlasPresentation.Exact.Cover
open Subgroup.CosetWordCertificate

def branch {α : Type*} (cutoff : Nat) (left right : Nat → α) (i : Nat) : α :=
  if i < cutoff then left i else right i

def unpack (pages : Nat → Nat) (bits i : Nat) : Nat :=
  (pages (i / 128) >>> (bits * (i % 128))) % (2 ^ bits)

def decode (a : Nat) : Letter Nat := (a / 2, a % 2 == 0)

end Sporadic.LeechRelated.HS.AtlasPresentation.Exact.Cover
