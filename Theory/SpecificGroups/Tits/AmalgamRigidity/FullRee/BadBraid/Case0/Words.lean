module
public import Theory.SpecificGroups.Tits.AmalgamRigidity.FullRee.BadBraid.Case0.wordCodeTable

/-! Kernel replay for a nonstandard binary Ree reflection pair.
Generated from the six sound coset-word rules; see `../source/README.md`. -/

@[expose] public section
namespace Tits.AmalgamRigidity.FullRee.BadBraid.Case0
open Subgroup.CosetWordCertificate
def word (i : Nat) : Word Nat := decodeWord (wordCode i) 48

end Tits.AmalgamRigidity.FullRee.BadBraid.Case0
