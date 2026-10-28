module

public import Theory.SpecificGroups.G2Five.AtlasBoundThirtyCertificate.defPairTable

/-! Generated kernel certificate; reproduce with `Theory/SpecificGroups/G2Five/AtlasBoundThirtySource/GenerateCertificate.py`.
Source: the thirty retained ATLAS words; see `AtlasBoundThirtySource/README.md`. -/

@[expose] public section
namespace G2Five.AtlasPresentation.ThirtyCertificate
open Subgroup.CosetWordCertificate

/-- Acyclic representatives, extended harmlessly beyond the finite input. -/
def definitions : Definitions (Fin 3) where
  parent n := min (defPair n).1 (n - 1)
  letter n := (defPair n).2
  parent_lt n := by
    have := Nat.min_le_right (defPair (n + 1)).1 (n + 1 - 1)
    omega

def relatorFin : Fin 31 → Word (Fin 3) := fun i => match i.1 with
  | 0 => [(0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true)]
  | 1 => [(1, true), (0, false), (0, false), (0, false), (1, true), (1, true), (0, false), (1, true), (0, false), (1, true), (0, true), (0, true), (1, false), (0, false)]
  | 2 => [(1, true), (1, true), (1, true), (0, true), (1, false), (0, false), (0, false), (1, false), (1, false), (0, false), (1, false), (1, false), (1, false), (1, false), (0, false)]
  | 3 => [(0, false), (1, true), (1, true), (0, false), (0, false), (1, false), (0, false), (1, true), (0, false), (1, true), (1, true), (0, false), (0, false), (1, false), (0, false), (1, true)]
  | 4 => [(1, true), (0, true), (1, true), (1, true), (1, true), (0, true), (1, true), (1, true), (1, true), (0, true), (1, true), (1, true), (1, true), (0, true), (1, true), (1, true)]
  | 5 => [(1, true), (0, true), (0, true), (1, true), (1, true), (0, true), (1, false), (0, true), (1, true), (0, true), (0, true), (1, true), (1, true), (0, true), (1, false), (0, true)]
  | 6 => [(1, true), (1, true), (1, true), (0, false), (1, true), (0, true), (0, true), (1, false), (0, false), (1, false), (1, false), (0, true), (1, true), (0, false), (1, true), (0, false), (1, true)]
  | 7 => [(1, false), (0, true), (1, true), (0, false), (0, false), (1, true), (0, false), (1, true), (1, true), (0, true), (1, true), (1, true), (1, true), (0, false), (1, false), (1, false), (0, true)]
  | 8 => [(0, true), (1, true), (1, true), (0, false), (1, true), (0, true), (0, true), (1, false), (1, false), (1, false), (0, true), (1, false), (0, false), (1, false), (0, true), (1, false), (0, true), (1, false)]
  | 9 => [(0, false), (1, true), (1, true), (0, false), (1, false), (0, false), (1, false), (0, false), (1, true), (1, true), (0, true), (1, true), (0, true), (0, true), (1, false), (1, false), (1, false), (0, false)]
  | 10 => [(0, true), (0, true), (0, true), (1, true), (0, true), (1, true), (1, true), (1, true), (1, true), (0, false), (1, false), (0, false), (0, false), (0, false), (1, true), (1, true), (1, true), (1, true)]
  | 11 => [(1, true), (0, true), (0, true), (0, true), (1, true), (0, true), (0, true), (0, true), (1, false), (0, true), (1, true), (0, true), (1, true), (1, true), (0, false), (1, false), (0, true), (1, true)]
  | 12 => [(1, false), (0, true), (1, false), (0, false), (0, false), (1, true), (1, true), (0, true), (1, false), (0, false), (1, false), (0, true), (0, true), (0, true), (1, false), (0, true), (0, true), (1, false)]
  | 13 => [(0, false), (1, true), (1, true), (0, true), (1, true), (1, true), (0, false), (1, false), (0, true), (1, true), (1, true), (1, true), (0, false), (0, false), (1, false), (0, true), (0, true), (0, true), (1, false)]
  | 14 => [(1, false), (0, true), (0, true), (0, true), (1, true), (0, true), (1, true), (0, false), (0, false), (1, false), (0, true), (1, false), (0, false), (0, false), (1, false), (0, true), (1, false), (1, false), (0, false)]
  | 15 => [(0, true), (1, true), (0, false), (1, false), (0, true), (0, true), (1, true), (1, true), (0, false), (1, false), (0, false), (0, false), (1, true), (0, true), (1, true), (1, true), (1, true), (0, false), (1, false)]
  | 16 => [(0, true), (1, false), (1, false), (0, false), (1, false), (0, false), (0, false), (0, false), (1, true), (0, true), (0, true), (0, true), (1, false), (1, false), (1, false), (0, false), (1, false), (1, false), (1, false)]
  | 17 => [(0, true), (0, true), (0, true), (1, false), (1, false), (1, false), (1, false), (0, true), (1, true), (0, true), (1, true), (1, true), (0, true), (1, false), (0, true), (1, false), (0, true), (0, true), (1, false)]
  | 18 => [(1, false), (0, false), (0, false), (1, true), (1, true), (0, false), (1, true), (0, true), (1, false), (1, false), (0, true), (0, true), (1, false), (0, false), (1, false), (0, false), (1, true), (1, true), (0, false)]
  | 19 => [(0, false), (1, false), (0, true), (1, false), (0, false), (1, false), (0, true), (1, false), (0, true), (1, true), (0, true), (1, true), (0, false), (0, false), (0, false), (1, false), (0, false), (1, false), (0, false)]
  | 20 => [(1, false), (1, false), (1, false), (0, false), (0, false), (0, false), (0, false), (1, false), (1, false), (0, false), (0, false), (1, true), (1, true), (1, true), (0, true), (1, false), (0, true), (0, true), (1, false)]
  | 21 => [(0, true), (0, true), (0, true), (1, true), (1, true), (1, true), (0, false), (1, true), (1, true), (0, false), (1, true), (0, false), (1, false), (0, false), (1, false), (0, false), (1, false), (0, true), (1, true)]
  | 22 => [(1, true), (0, false), (0, false), (0, false), (1, true), (0, true), (1, false), (1, false), (0, true), (0, true), (1, true), (0, false), (0, false), (0, false), (1, false), (0, false), (0, false), (0, false), (0, false)]
  | 23 => [(0, true), (0, true), (1, false), (0, true), (1, false), (0, false), (1, true), (1, true), (0, true), (0, true), (1, false), (1, false), (1, false), (1, false), (0, false), (1, true), (0, false), (0, false), (1, false)]
  | 24 => [(1, true), (0, true), (0, true), (1, true), (0, false), (1, false), (0, true), (1, false), (0, false), (1, false), (0, false), (1, true), (1, true), (0, true), (1, false), (1, false), (0, false), (1, true), (0, true)]
  | 25 => [(0, true), (1, false), (0, false), (1, true), (1, true), (0, true), (0, true), (0, true), (1, true), (1, true), (1, true), (1, true), (0, true), (0, true), (1, false), (0, true), (1, false), (0, false), (1, true)]
  | 26 => [(1, false), (0, true), (0, true), (0, true), (0, true), (0, true), (1, true), (0, false), (0, false), (1, true), (1, true), (0, false), (0, false), (0, false), (0, false), (0, false), (1, false), (1, false), (0, true), (0, true)]
  | 27 => [(1, true), (0, false), (1, false), (0, true), (0, true), (1, false), (0, true), (0, true), (1, false), (1, false), (0, false), (1, false), (0, true), (0, true), (1, true), (0, true), (0, true), (0, true), (1, false), (0, true)]
  | 28 => [(1, false), (0, false), (1, true), (0, true), (0, true), (1, false), (1, false), (1, false), (1, false), (0, false), (0, false), (1, false), (0, true), (0, true), (1, false), (0, true), (1, false), (0, true), (1, false), (0, true)]
  | 29 => [(0, false), (0, false), (0, false), (1, true), (0, false), (0, false), (1, true), (1, true), (0, true), (1, false), (1, false), (0, false), (1, true), (0, false), (1, true), (1, true), (1, true), (0, false), (1, false), (0, false)]
  | 30 => [(1, true), (1, true), (1, true), (1, true), (2, false)]
  | _ => []

def relatorWords (r : Nat) : Word (Fin 3) :=
  if h : r < 31 then relatorFin ⟨r, h⟩ else []

def context : Context (Fin 3) :=
  ⟨definitions.parent, definitions.letter, relatorWords,
    fun a => decide (a = (0, true) ∨ a = (2, true))⟩

end G2Five.AtlasPresentation.ThirtyCertificate
