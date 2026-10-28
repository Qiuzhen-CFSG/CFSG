module

public import Theory.SpecificGroups.Janko3.RecognitionPresentation.OrderBound.M1Finite.Relations.LongWords.Seventeen
public import Theory.SpecificGroups.Janko3.RecognitionPresentation.OrderBound.M1Finite.Relations.LongWords

/-!
# Discharging the seventeen-letter bridge in the long local relations

The original presentation now supplies the seventeen-letter identity. Apply
it to the existing long-word replay at the literal generators `x`, `m1Word x y`
and `auxiliaryWord x y`. The separate coordinate identity remains with the
long-local-relations assembly owner.

Source: ATLAS J3G1-P1,
https://brauer.maths.qmul.ac.uk/Atlas/spor/J3/mag/J3G1-P1.M .
-/

namespace Sporadic.Janko3.RecognitionPresentation.OrderBound.M1Finite.Relations
open LongWords

/-- All three long local relators, after discharging the seventeen-letter
bridge. Only the independently produced sixth power and coordinate remain. -/
public theorem long_relations_of_sixth_and_coordinate
    (h6 : (x * (m1Word x y)⁻¹) ^ 6 = 1)
    (ht : auxiliaryWord x y = coordinateWord x (m1Word x y)) :
    ∀ i : Fin 3, LocalPresentation.relator x (m1Word x y)
      ⟨i.val + 3, by omega⟩ = 1 :=
  long_relations_of_sixth_and_bridges h6 ht (seventeen_of_sixth h6)

end Sporadic.Janko3.RecognitionPresentation.OrderBound.M1Finite.Relations
