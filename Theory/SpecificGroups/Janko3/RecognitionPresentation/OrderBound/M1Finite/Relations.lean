module

public import Theory.SpecificGroups.Janko3.RecognitionPresentation.OrderBound.M1Finite.Relations.Interpretation

/-!
# Derivation interface for the four abstract J₃ local relations

`Relations.Calculus` proves the sound word operations used by a recorded
Schreier elimination. `Relations.Interpretation` connects the output with the
literal pair `x,(y*x)^5*y⁻¹*x*y*x*y` and the six published local relators.

The retained first trace still needs its full Lean replay, and the other three
identities still need derivations. Consequently this module does not yet assert
`remaining_relations`. The final assembly remains here, independently of the
separate local-presentation order certificate.

Source: ATLAS J3G1-P1,
https://brauer.maths.qmul.ac.uk/Atlas/spor/J3/mag/J3G1-P1.M .
-/
