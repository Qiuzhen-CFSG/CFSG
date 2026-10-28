module

public import Theory.SpecificGroups.Janko3.RecognitionPresentation.OrderBound.M1Finite.Relations.LongWords.Adapter

/-!
# The three long local relations for the abstract J₃ presentation

The checked rewrite replay gives the three exact local words from the sixth
power and two concrete bridge identities for the literal auxiliary generator.
The three other short auxiliary relations are proved from the original eight
relators in `LongWords.Bridge`.

The coordinate and seventeen-letter bridge identities remain premises below.
Consequently this is not yet `long_relations_of_sixth`. This task retains their
final discharge and assembly; neither a permutation model nor a group-order
bound is used as a proof of a bridge premise.

Source: ATLAS J3G1-P1,
https://brauer.maths.qmul.ac.uk/Atlas/spor/J3/mag/J3G1-P1.M .
-/

namespace Sporadic.Janko3.RecognitionPresentation.OrderBound.M1Finite.Relations
open LongWords

/-- Literal application of the long-word replay. The two bridge identities
remain to be derived in the original abstract presentation. -/
public theorem long_relations_of_sixth_and_bridges
    (h6 : (x * (m1Word x y)⁻¹) ^ 6 = 1)
    (ht : auxiliaryWord x y = coordinateWord x (m1Word x y))
    (h17 : seventeenWord x (m1Word x y) (auxiliaryWord x y) = 1) :
    ∀ i : Fin 3, LocalPresentation.relator x (m1Word x y)
      ⟨i.val + 3, by omega⟩ = 1 :=
  long_relations_of_bridge_inputs x (m1Word x y) (auxiliaryWord x y)
    (presentation_satisfies 0) (m1Word_four presentation_satisfies) h6
    (short_three x y presentation_satisfies)
    (short_commuting x y presentation_satisfies)
    (short_four x y presentation_satisfies) h17 ht

end Sporadic.Janko3.RecognitionPresentation.OrderBound.M1Finite.Relations
