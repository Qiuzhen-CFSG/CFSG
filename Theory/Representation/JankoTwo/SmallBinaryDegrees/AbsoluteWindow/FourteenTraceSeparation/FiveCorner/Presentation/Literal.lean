module

public import Theory.Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.FourteenTraceSeparation.FiveLocal
public import Theory.Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.FourteenTraceSeparation.FiveCorner.Certificate
public import Theory.Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.FourteenTraceSeparation.FiveCorner.Presentation.Subgroup
public import Theory.Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.FourteenTraceSeparation.FiveCorner.Presentation.Operators

/-!
# Literal generators and the Hall--Janko coordinate contract

The fixed order-25 subgroup is proved directly from its ATLAS words. Every
proposed generator below is a sum of actual elements e g e in its norm corner;
the identity of this ring is e. Faithful additive coordinates intertwining
right multiplication allow the independent finite word-span and polynomial
certificates to establish the requested literal presentation.

This module publishes the literal generators and the coordinate contract
without importing their assembly owner. It does not assert the presentation
until the coordinate realization and finite certificates have been proved. Source application: Guralnick--Malle
Proposition 5.1, and corrected Hiss--Malle Table 2, degree-fourteen J₂ entry.
-/

@[expose] public noncomputable section
namespace Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.FiveCorner.Presentation
open Sporadic.LeechRelated.J2

/-- A literal condensed group element, belonging to the actual norm corner. -/
def condensed (he : IsIdempotentElem (fiveNorm subgroup)) (g : Carrier) : he.Corner :=
  ⟨fiveNorm subgroup * MonoidAlgebra.single g 1 * fiveNorm subgroup,
    ⟨MonoidAlgebra.single g 1, rfl⟩⟩

/-- The nine proposed elements of the actual corner, with no abstract algebra
or dimension comparison substituted for that corner. -/
def generators (he : IsIdempotentElem (fiveNorm subgroup)) : Fin 9 → he.Corner :=
  fun i => ((generatorWords i).map fun w => condensed he (word w)).sum

/-- The identity used by the certificate is the subgroup norm itself. -/
theorem one_val (he : IsIdempotentElem (fiveNorm subgroup)) :
    (1 : he.Corner).val = fiveNorm subgroup := rfl

/-- Missing geometric input: faithful additive coordinates on the literal
corner with the stated identity and all nine right multiplication operations.
Surjectivity is unnecessary here; it will follow from the finite word span. -/
def LiteralCoordinates : Prop :=
  ∀ he : IsIdempotentElem (fiveNorm subgroup),
    ∃ F : he.Corner →+ Coordinates, Function.Injective F ∧ F 1 = seed ∧
      ∀ z i, F (z * generators he i) = operator i (F z)

end Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.FiveCorner.Presentation
