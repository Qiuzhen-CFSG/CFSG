module
public import Theory.SpecificGroups.Tits.AmalgamRigidity.FullRee.BadBraid.Case0.factCodeTable
public import Theory.SpecificGroups.Tits.AmalgamRigidity.FullRee.BadBraid.Case0.operationCodeTable
public import Theory.SpecificGroups.Tits.AmalgamRigidity.FullRee.BadBraid.Case0.Words

/-! Kernel replay for a nonstandard binary Ree reflection pair.
Generated from the six sound coset-word rules; see `../source/README.md`. -/

@[expose] public section
namespace Tits.AmalgamRigidity.FullRee.BadBraid.Case0
open Subgroup.CosetWordCertificate

def facts (i : Nat) : FactData Nat :=
 let v := factCode i
 ⟨v%131072, word (v/17179869184), v/131072%131072⟩
def instructions (i : Nat) : Instruction Nat :=
 let v := operationCode i
 let a := v/8%262144
 let b := v/2097152
 match v%8 with
 | 0 => .refl a
 | 1 => .defining a
 | 2 => .subgroup (decodeLetter a)
 | 3 => .relator a b
 | 4 => .reverse a
 | _ => .compose a b

end Tits.AmalgamRigidity.FullRee.BadBraid.Case0
