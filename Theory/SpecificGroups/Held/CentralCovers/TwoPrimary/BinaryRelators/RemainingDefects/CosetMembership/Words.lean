module

public import Mathlib.Data.Fin.Basic
public import Mathlib.Data.List.Rotate

/-!
# Literal words for the Held centralizer membership certificate

Columns `0,1,2,3` denote `x,x⁻¹,y,y⁻¹`. The seven relators are the
uncommented words in John Bray's ATLAS `HeG1-P1.M`, retained in
`Theory/SpecificGroups/Held/Model/Source/`. The nine subgroup words are
exactly the seeds in `RemainingDefects.Centralizer`. These are syntactic
data; the connection to the group words is checked in `Interpretation`.
-/

@[expose] public section
namespace Held.CentralCovers.TwoPrimary.BinaryRelators.RemainingDefects.CosetMembership
abbrev Word := List (Fin 4)

def flip : Fin 4 → Fin 4
  | 0 => 1
  | 1 => 0
  | 2 => 3
  | _ => 2

def inverse (w : Word) : Word := (w.map flip).reverse

def relator : Fin 7 → Word
  | 0 => [0, 0]
  | 1 => [2, 2, 2, 2, 2, 2, 2]
  | 2 => [0, 2, 0, 2, 0, 2, 0, 2, 0, 2, 0, 2, 0, 2, 0, 2, 0, 2, 0, 2, 0, 2, 0, 2, 0, 2, 0, 2, 0, 2, 0, 2, 0, 2]
  | 3 => [1, 3, 1, 3, 1, 2, 1, 3, 1, 3, 0, 2, 0, 2, 0, 3, 0, 2, 0, 2]
  | 4 => [1, 3, 3, 3, 0, 2, 2, 2, 1, 3, 3, 3, 0, 2, 2, 2, 1, 3, 3, 3, 0, 2, 2, 2, 1, 3, 3, 3, 0, 2, 2, 2, 1, 3, 3, 3, 0, 2, 2, 2]
  | 5 => [1, 3, 0, 2, 1, 3, 0, 2, 1, 3, 0, 2, 1, 3, 0, 2, 1, 3, 0, 2, 1, 3, 0, 2]
  | _ => [0, 2, 0, 2, 0, 2, 0, 2, 0, 2, 2, 0, 3, 3, 3, 0, 2, 0, 2, 0, 3, 0, 2, 2, 2, 0, 3, 3, 0, 2, 2]

def seed : Fin 9 → Word
  | 0 => [0]
  | 1 => [2, 0, 2, 0, 3, 0, 2, 0, 2]
  | 2 => [1, 3, 0, 2, 1, 3, 0, 2, 1, 3, 0, 2]
  | 3 => [1, 2, 0, 3, 1, 2, 0, 3, 1, 2, 0, 3]
  | 4 => [2, 2, 2, 1, 3, 3, 3, 0, 2, 2, 2, 1, 3, 3, 3, 0, 2, 2, 2, 2, 2, 2, 1, 3, 3, 3, 0, 2, 2, 2, 1, 3, 3, 3, 0, 2, 2, 2]
  | 5 => [3, 3, 3, 1, 2, 2, 2, 0, 3, 3, 3, 1, 2, 2, 2, 0, 3, 3, 3, 0, 2, 2, 2, 1, 3, 3, 3, 0, 2, 2, 2, 1, 3, 3, 3, 0, 2, 2, 2]
  | 6 => [3, 3, 3, 1, 2, 2, 2, 0, 3, 3, 3, 1, 2, 2, 2, 0, 3, 3, 3, 2, 0, 2, 0, 3, 0, 2, 0, 2, 2, 2, 2, 1, 3, 3, 3, 0, 2, 2, 2, 1, 3, 3, 3, 0, 2, 2, 2]
  | 7 => [3, 3, 3, 1, 2, 2, 2, 0, 3, 3, 3, 1, 2, 2, 2, 0, 3, 3, 3, 1, 3, 0, 2, 1, 3, 0, 2, 1, 3, 0, 2, 2, 2, 2, 1, 3, 3, 3, 0, 2, 2, 2, 1, 3, 3, 3, 0, 2, 2, 2]
  | _ => [3, 3, 3, 1, 2, 2, 2, 0, 3, 3, 3, 1, 2, 2, 2, 0, 3, 3, 3, 1, 2, 0, 3, 1, 2, 0, 3, 1, 2, 0, 3, 2, 2, 2, 1, 3, 3, 3, 0, 2, 2, 2, 1, 3, 3, 3, 0, 2, 2, 2]

def target : Word := [2, 2, 2, 1, 3, 3, 3, 0, 2, 2, 2, 1, 3, 3, 3, 0, 2, 2, 2]

end Held.CentralCovers.TwoPrimary.BinaryRelators.RemainingDefects.CosetMembership
