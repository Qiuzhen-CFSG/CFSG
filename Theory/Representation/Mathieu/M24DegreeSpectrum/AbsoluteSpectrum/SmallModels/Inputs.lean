module

public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.Contracts
public import Mathlib.Algebra.Field.ZMod

/-!
# The remaining degree-forty-four construction

The code and cocode supply two inequivalent simple modules of degree eleven.
The small-spectrum construction additionally needs two inequivalent simple
modules of degree forty-four. Dimension then separates the pairs.

This is an existence contract for actual representations of the native
Witt-design M24, with no completeness or section-placement premise.
It is not asserted here. The source for the candidates is James,
The modular characters of the Mathieu groups, J. Algebra 27 (1973),
57--111; compare GM02, Proposition 5.1, manuscript p.17.
-/

@[expose] public section
namespace Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.SmallModels
open Sporadic.Mathieu
universe v

/-- Two actual inequivalent simple forty-four-dimensional modules over every
closed characteristic-two field. The parent small-family assembly must
construct and supply this remaining input. -/
def FortyFourModelsExist : Prop :=
  ∀ (F : Type v) [Field F] [IsAlgClosed F] [CharP F 2],
    ∃ ρ : Fin 2 → Representation F M24 (Fin 44 → F),
      (∀ i, IsIrreducible (ρ i)) ∧
      Pairwise fun i j => IsEmpty ((ρ i).Equiv (ρ j))

/-- A binary certificate suffices: two actual absolutely irreducible modules
of degree forty-four, inequivalent with the native M24 marking. -/
def BinaryFortyFourModelsExist : Prop :=
  ∃ ρ : Fin 2 → Representation (ZMod 2) M24 (Fin 44 → ZMod 2),
    (∀ i, IsAbsolutelyIrreducible (ρ i)) ∧
    Pairwise fun i j => IsEmpty ((ρ i).Equiv (ρ j))

end Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.SmallModels
