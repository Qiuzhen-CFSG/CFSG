module

public import Theory.GroupTheory.CosetWordCertificate

/-! Generated kernel certificate; reproduce with `Theory/SpecificGroups/Thompson/Model/Simplicity/NormalGenerationHigh/source/generate.py`.
Source word: ATLAS Th conjugacy table, https://brauer.maths.qmul.ac.uk/Atlas/v3/spor/Th/. -/

@[expose] public section
namespace Thompson.Simplicity.Word31Certificate
open Subgroup.CosetWordCertificate

/-- Balanced explicit lookup avoids reconstructing a deduction history. -/
def lookupBranch {α : Type*} (cutoff : Nat) (left right : Nat → α) (i : Nat) : α :=
  if i < cutoff then left i else right i

end Thompson.Simplicity.Word31Certificate
