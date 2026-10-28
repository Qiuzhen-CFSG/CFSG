module

public import Theory.SpecificGroups.Janko3.RecognitionPresentation.OrderBound.M1Finite.Relations.Interpretation
public import Theory.SpecificGroups.Janko3.RecognitionPresentation.OrderBound.M1Finite.Relations.SixthPower.Stage018

/-!
# The sixth-power identity in the original J₃ presentation

The retained 88,429-node derivation is checked one relator operation at a time.
Its auxiliary generators are literal ambient words. The terminal word is
`sixthTraceWord`; the source involution relation and cyclic conjugation identify
it with `(x * (m1Word x y)⁻¹)^6`. No ambient finiteness or model is assumed.

Source: ATLAS J3G1-P1, https://brauer.maths.qmul.ac.uk/Atlas/spor/J3/mag/J3G1-P1.M .
-/

namespace Sporadic.Janko3.RecognitionPresentation.OrderBound.M1Finite.Relations

/-- The third local relator follows from the original eight ambient relators. -/
public theorem local_relation_two : LocalPresentation.relator x (m1Word x y) 2 = 1 :=
  local_two_of_checked_word SixthPower.auxiliary SixthPower.auxiliary_x
    SixthPower.auxiliary_z SixthPower.proof88428

end Sporadic.Janko3.RecognitionPresentation.OrderBound.M1Finite.Relations
