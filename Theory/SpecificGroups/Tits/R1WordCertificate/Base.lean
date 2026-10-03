module

public import Theory.SpecificGroups.Tits.R1Presentation
public import Theory.GroupTheory.CosetWordCertificate

/-! Generated kernel certificate; reproduce with `refs/original/n-group-global/parrott-r1-word-certificate/generate.py`.
Source: Parrott (1972), §5, p. 683; see `parrott-tits-presentation.md`. -/

@[expose] public section
namespace Tits.R1WordCertificate
open Subgroup.CosetWordCertificate

/-- Balanced explicit lookup avoids reconstructing a deduction history. -/
def lookupBranch {α : Type*} (cutoff : Nat) (left right : Nat → α) (i : Nat) : α :=
  if i < cutoff then left i else right i

end Tits.R1WordCertificate
