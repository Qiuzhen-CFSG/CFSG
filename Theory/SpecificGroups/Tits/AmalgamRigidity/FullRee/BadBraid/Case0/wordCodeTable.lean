module
public import Theory.SpecificGroups.Tits.AmalgamRigidity.FullRee.BadBraid.Case0.wordCodeData000

/-! Kernel replay for a nonstandard binary Ree reflection pair.
Generated from the six sound coset-word rules; see `../source/README.md`. -/

@[expose] public section
namespace Tits.AmalgamRigidity.FullRee.BadBraid.Case0
open Subgroup.CosetWordCertificate
def wordCode : Nat → Nat :=
 (branch 640 (branch 256 (branch 128 wordCode0 wordCode128) (branch 384 wordCode256 (branch 512 wordCode384 wordCode512))) (branch 896 (branch 768 wordCode640 wordCode768) (branch 1024 wordCode896 (branch 1152 wordCode1024 wordCode1152))))

end Tits.AmalgamRigidity.FullRee.BadBraid.Case0
