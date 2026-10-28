module
public import Theory.SpecificGroups.Tits.AmalgamRigidity.FullRee.BadBraid.Case2.definitionCodeTable

/-! Kernel replay for a nonstandard binary Ree reflection pair.
Generated from the six sound coset-word rules; see `../source/README.md`. -/

@[expose] public section
namespace Tits.AmalgamRigidity.FullRee.BadBraid.Case2
open Subgroup.CosetWordCertificate

def definitions : Definitions Nat where
 parent n := min (definitionCode n / 16) (n-1)
 letter n := decodeLetter (definitionCode n % 16)
 parent_lt n := by have := Nat.min_le_right (definitionCode (n+1)/16) (n+1-1); omega

def badWord : Word Nat := [(2, true), (2, true), (3, true), (0, false), (4, true), (0, true), (2, true), (2, true), (3, true), (0, false), (4, true), (0, true), (2, true), (2, true), (3, true), (0, false), (4, true), (0, true), (2, true), (2, true), (3, true), (0, false), (4, true), (0, true), (2, true), (2, true), (3, true), (0, false), (4, true), (0, true), (2, true), (2, true), (3, true), (0, false), (4, true), (0, true), (2, true), (2, true), (3, true), (0, false), (4, true), (0, true), (2, true), (2, true), (3, true), (0, false), (4, true), (0, true)]
def relatorWords (i : Nat) : Word Nat :=
 if h : i < 39 then relator ⟨i,h⟩ else if i=39 then badWord else []
def allowed (a : Letter Nat) : Bool := a.2 && Nat.blt a.1 4

def context : Context Nat := ⟨definitions.parent, definitions.letter, relatorWords, allowed⟩

end Tits.AmalgamRigidity.FullRee.BadBraid.Case2
