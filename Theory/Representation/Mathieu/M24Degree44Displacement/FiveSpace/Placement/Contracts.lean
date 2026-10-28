module

public import Theory.Representation.Mathieu.M24Degree44Displacement.FiveSpace.Exterior
public import Theory.Representation.AbsolutelyIrreducible

/-!
# Binary models with native Golay exterior sections

The construction input consists of four actual, pairwise inequivalent,
absolutely irreducible binary representations. Their degrees are eleven or
forty-four, and each degree-forty-four member comes with a literal section of
one of the two native Golay exterior squares. No arbitrary representation
is classified in this input.

`Placement` proves completeness using eight larger simple modules and the
odd-order conjugacy-class bound. A coefficient projection descends a simple
constituent of an arbitrary scalar extension, so absolute irreducibility of
the representation being classified is not an additional premise.

Source: G. D. James, The modular characters of the Mathieu groups,
J. Algebra 27 (1973), 57--111; the degree-forty-four application is
Guralnick--Malle, Classification of 2F-modules I, Proposition 5.1,
M₂₄ paragraph, manuscript p.17.
-/

@[expose] public section
namespace Representation.MathieuM24Degree44.FiveSpace.Placement
open Sporadic.Mathieu

/-- A construction contract on four binary models, including actual native
section maps for their degree-forty-four members. This does not assert
exhaustion and is not yet instantiated. -/
def BinarySectionModels : Prop :=
  ∃ (d : Fin 4 → ℕ) (ρ : ∀ i, Representation (ZMod 2) M24 (Fin (d i) → ZMod 2)),
    (∀ i, (ρ i).IsAbsolutelyIrreducible) ∧
    (Pairwise fun i j => IsEmpty ((ρ i).Equiv (ρ j))) ∧
    (∀ i, d i = 11 ∨ d i = 44) ∧
    ∀ i, d i = 44 → IsSectionOf (ρ i) codeExterior ∨ IsSectionOf (ρ i) cocodeExterior

end Representation.MathieuM24Degree44.FiveSpace.Placement
