module

public import Theory.Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.FourteenTraceSeparation.FiveLocal
public import Theory.Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.FourteenTraceSeparation.FiveCorner.Certificate
public import Theory.Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.FourteenTraceSeparation.FiveCorner.Presentation.Literal

/-!
# Literal generators and coordinate assembly for the Hall--Janko corner

The fixed order-25 subgroup is proved directly from its ATLAS words. Every
proposed generator below is a sum of actual elements e g e in its norm corner;
the identity of this ring is e. Faithful additive coordinates intertwining
right multiplication allow the independent finite word-span and polynomial
certificates to establish the requested literal presentation.

`presentation_of_coordinates` leaves those three mathematical inputs explicit.
It does not assert the presentation until the coordinate realization and the
finite certificates have been proved. Source application: Guralnick--Malle
Proposition 5.1, and corrected Hiss--Malle Table 2, degree-fourteen J₂ entry.
-/

@[expose] public noncomputable section
namespace Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.FiveCorner.Presentation
open Sporadic.LeechRelated.J2

/-- Assemble the literal presentation from geometric coordinates and the two
finite certificates. Every extra premise remains explicit. -/
theorem presentation_of_coordinates (hcoords : LiteralCoordinates)
    (hspan : CoordinateWordSpan) (hrel : CoordinateRelations) :
    Certificate.LiteralPresentation := by
  refine ⟨subgroup, card_subgroup, ?_⟩
  intro he
  obtain ⟨F, hinj, hone, hmul⟩ := hcoords he
  refine ⟨generators he, ?_, ?_⟩
  · apply closure_eq_top_of_word_span (generators he) (fun i => operator i) F hmul hinj
    simpa only [CoordinateWordSpan, hone] using hspan
  · apply satisfies_of_relations (generators he) (fun i => operator i) F hmul hinj
    simpa only [CoordinateRelations, hone] using hrel

end Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.FiveCorner.Presentation
