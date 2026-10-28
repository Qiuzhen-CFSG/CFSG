module

public import Theory.SpecificGroups.Janko3.RecognitionPresentation.OrderBound.M1Finite.Relations.LongWords.Bridge
public import Theory.SpecificGroups.Janko3.RecognitionPresentation.OrderBound.M1Finite.Relations.LongWords.Seventeen.Reduction

/-!
# The seventeen-letter identity in the original J₃ presentation

A 59-equation dependency slice of ambient Knuth–Bendix completion reduces
this word to one. All leaves come from the original relators, so the identity
holds for every satisfying pair, without the sixth-power hypothesis. The final
wrapper supplies the exact bridge used by the long-local-relations assembly.

Source: ATLAS J3G1-P1,
https://brauer.maths.qmul.ac.uk/Atlas/spor/J3/mag/J3G1-P1.M .
-/

namespace Sporadic.Janko3.RecognitionPresentation.OrderBound.M1Finite.Relations.LongWords

/-- The seventeen-letter bridge follows directly from the eight source relators. -/
public theorem seventeen_of_satisfies {G : Type*} [Group G]
    (a b : G) (h : Satisfies a b) :
    seventeenWord a (m1Word a b) (auxiliaryWord a b) = 1 := by
  let g := letters a b
  have hx : a ^ 2 = 1 := h 0
  have hxi : a⁻¹ = a := inv_eq_of_mul_eq_one_right (by simpa only [pow_two] using hx)
  have hi := letters_inverse a b hx
  have hxw : readWord g [0] = a := by simp [g, letters]
  have hz : readWord g [1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 2, 0, 1, 0, 1] = m1Word a b := by
    simp only [readWord_cons, readWord_nil, g, letters, m1Word,
      pow_succ, pow_zero, mul_one, one_mul, mul_assoc]
  have ht : readWord g [0, 1, 0, 2, 0, 2, 0, 2, 0, 2, 0, 2, 0, 1, 0, 1, 0, 1, 0, 1, 0, 2] = auxiliaryWord a b := by
    simp only [readWord_cons, readWord_nil, g, letters, auxiliaryWord,
      pow_succ, pow_zero, mul_one, one_mul, hxi, mul_assoc]
  have hdone := Seventeen.output (Seventeen.inputs a b h)
  change readWord g ((inverseWord [1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 2, 0, 1, 0, 1]) ++ ([0]) ++ (inverseWord [0, 1, 0, 2, 0, 2, 0, 2, 0, 2, 0, 2, 0, 1, 0, 1, 0, 1, 0, 1, 0, 2]) ++ ([0]) ++ (inverseWord [0, 1, 0, 2, 0, 2, 0, 2, 0, 2, 0, 2, 0, 1, 0, 1, 0, 1, 0, 1, 0, 2]) ++ ([1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 2, 0, 1, 0, 1]) ++ ([0]) ++ (inverseWord [1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 2, 0, 1, 0, 1]) ++ ([0, 1, 0, 2, 0, 2, 0, 2, 0, 2, 0, 2, 0, 1, 0, 1, 0, 1, 0, 1, 0, 2]) ++ ([0]) ++ ([1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 2, 0, 1, 0, 1]) ++ ([0]) ++ (inverseWord [1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 2, 0, 1, 0, 1]) ++ ([0, 1, 0, 2, 0, 2, 0, 2, 0, 2, 0, 2, 0, 1, 0, 1, 0, 1, 0, 1, 0, 2]) ++ ([0]) ++ ([1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 2, 0, 1, 0, 1]) ++ ([0])) = 1 at hdone
  simpa only [readWord_append, readWord_inverse g hi, hxw, hz, ht,
    seventeenWord] using hdone

/-- The precise bridge interface for the long-local-relations consumer. -/
public theorem seventeen_of_sixth (h6 : (x * (m1Word x y)⁻¹) ^ 6 = 1) :
    seventeenWord x (m1Word x y) (auxiliaryWord x y) = 1 := by
  have _ := h6
  exact seventeen_of_satisfies x y presentation_satisfies

end Sporadic.Janko3.RecognitionPresentation.OrderBound.M1Finite.Relations.LongWords
