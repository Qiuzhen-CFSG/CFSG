module

public import Theory.SpecificGroups.G2Five.AtlasBoundThirtyChain
public import Theory.GroupTheory.CosetWordCertificate

/-! Generated kernel certificate; reproduce with `Theory/SpecificGroups/G2Five/AtlasBoundThirtySource/GenerateCertificate.py`.
Source: the thirty retained ATLAS words; see `AtlasBoundThirtySource/README.md`. -/

@[expose] public section
namespace G2Five.AtlasPresentation.ThirtyCertificate
open Subgroup.CosetWordCertificate

/-- Balanced explicit lookup avoids reconstructing a deduction history. -/
def lookupBranch {α : Type*} (cutoff : Nat) (left right : Nat → α) (i : Nat) : α :=
  if i < cutoff then left i else right i

end G2Five.AtlasPresentation.ThirtyCertificate
