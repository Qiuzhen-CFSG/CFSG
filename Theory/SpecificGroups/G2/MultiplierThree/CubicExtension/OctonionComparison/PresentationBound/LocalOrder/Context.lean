module

public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalOrder.defPairTable

/-! Generated kernel certificate; reproduce with `Theory/SpecificGroups/G2/MultiplierThree/CubicExtension/OctonionComparison/PresentationBound/LocalOrder/source/Generate.py`.
Source: the seven literal local words; see `../source/README.md`. -/

@[expose] public section
namespace Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalOrder
open Subgroup.CosetWordCertificate

/-- Acyclic representatives, extended harmlessly beyond the finite input. -/
def definitions : Definitions (Bool) where
  parent n := min (defPair n).1 (n - 1)
  letter n := (defPair n).2
  parent_lt n := by
    have := Nat.min_le_right (defPair (n + 1)).1 (n + 1 - 1)
    omega

def relatorFin : Fin 7 → Word Bool := localRelatorLetters

def relatorWords (r : Nat) : Word (Bool) :=
  if h : r < 7 then relatorFin ⟨r, h⟩ else []

def context : Context (Bool) :=
  ⟨definitions.parent, definitions.letter, relatorWords,
    fun a => decide (a = (true, true))⟩

end Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalOrder
