module

public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.Alphabet
public import Theory.GroupTheory.CosetWordCertificate.Schreier

/-!
# The fixed 364-vertex Schreier data

Generated from the retained ATLAS max3 coset discovery table. These are only
word and table definitions; their required identities are checked separately.
See `source/README.md` for provenance and reproduction.
-/

@[expose] public section
namespace Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.SchreierCover

def lookup {α : Type*} (cutoff : Nat) (left right : Nat → α) (i : Nat) : α :=
  if i < cutoff then left i else right i

end Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.SchreierCover
