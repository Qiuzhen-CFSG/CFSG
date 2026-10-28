module

public import Theory.SpecificGroups.Thompson.Model.Simplicity.NormalGenerationHigh.Word31Certificate.defPairTable

/-! Generated kernel certificate; reproduce with `Theory/SpecificGroups/Thompson/Model/Simplicity/NormalGenerationHigh/source/generate.py`.
Source word: ATLAS Th conjugacy table, https://brauer.maths.qmul.ac.uk/Atlas/v3/spor/Th/. -/

@[expose] public section
namespace Thompson.Simplicity.Word31Certificate
open Subgroup.CosetWordCertificate

/-- Acyclic representatives, extended harmlessly beyond the finite input. -/
def definitions : Definitions (Fin 2) where
  parent n := min (defPair n).1 (n - 1)
  letter n := (defPair n).2
  parent_lt n := by
    have := Nat.min_le_right (defPair (n + 1)).1 (n + 1 - 1)
    omega

def relatorFin : Fin 4 → Word (Fin 2) := fun i => match i.1 with
  | 0 => [(0, true), (0, true)]
  | 1 => [(1, true), (1, true), (1, true)]
  | 2 => [(0, true), (1, true), (0, true), (1, true), (0, true), (1, true), (0, true), (1, true), (0, true), (1, true), (0, true), (1, true), (0, true), (1, true), (0, true), (1, true), (0, true), (1, true), (0, true), (1, true), (0, true), (1, true), (0, true), (1, true), (0, true), (1, true), (0, true), (1, true), (0, true), (1, true), (0, true), (1, true), (0, true), (1, true), (0, true), (1, true), (0, true), (1, true)]
  | 3 => [(0, true), (1, true), (0, true), (1, true), (0, true), (1, true), (0, true), (1, true), (0, true), (1, true), (0, true), (1, true), (0, true), (1, true), (1, true), (0, true), (1, true), (1, true), (0, true), (1, true), (0, true), (1, true), (0, true), (1, true), (0, true), (1, true), (0, true), (1, true), (1, true), (0, true), (1, true), (0, true), (1, true), (0, true), (1, true), (0, true), (1, true), (0, true), (1, true), (0, true), (1, true), (0, true), (1, true), (0, true), (1, true), (1, true)]
  | _ => []

def relatorWords (r : Nat) : Word (Fin 2) :=
  if h : r < 4 then relatorFin ⟨r, h⟩ else []

def context : Context (Fin 2) :=
  ⟨definitions.parent, definitions.letter, relatorWords,
    fun _ => false⟩

end Thompson.Simplicity.Word31Certificate
