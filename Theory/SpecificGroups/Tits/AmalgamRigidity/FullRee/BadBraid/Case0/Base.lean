module
public import Theory.SpecificGroups.Tits.AmalgamRigidity.FullRee.BadBraid.Relators
public import Theory.GroupTheory.CosetWordCertificateBoolean

/-! Kernel replay for a nonstandard binary Ree reflection pair.
Generated from the six sound coset-word rules; see `../source/README.md`. -/

@[expose] public section
namespace Tits.AmalgamRigidity.FullRee.BadBraid.Case0
open Subgroup.CosetWordCertificate

def branch {α : Type*} (cut : Nat) (a b : Nat → α) (i : Nat) : α :=
  if i < cut then a i else b i

def decodeWord (v : Nat) : Nat → Word Nat
 | 0 => []
 | k+1 => if v=0 then [] else decodeLetter (v%16-1) :: decodeWord (v/16) k

end Tits.AmalgamRigidity.FullRee.BadBraid.Case0
