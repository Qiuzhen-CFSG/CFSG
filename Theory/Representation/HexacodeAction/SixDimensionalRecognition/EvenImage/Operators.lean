module
public import Theory.Representation.HexacodeAction.SixDimensionalRecognition.EvenImage.Generators
/-!
# Concrete operators for even image recognition

The actual generating pair acts in the existing F₄ coordinates by
`A = !![1,1,1; 1,0,0; 0,1,0]` and
`B = !![0,0,1; omega,0,0; 0,omega²,0]`.
The coordinate formulas are checked on the systematic code encoder and
transported to every codeword by the existing reconstruction theorem.
They fix the literal operators for order-four normalization and the remaining
finite matrix-pair certificate, without replacing the hexacode carrier.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, K.1.3,
printed p.453 (PDF p.464). The systematic code and monomial formulas are
from the licensed ATLAS ports under `Theory.AtlasPort.OtherSporadic.Codes`.
-/

@[expose] public section
open Atlas.Codes Subgroup
namespace Representation.Hexacode.SixDimensional.EvenImage

/-- The fixed order-four operator on the actual code carrier. -/
noncomputable def fieldGenerator : FieldGL := evenFieldAction generatorA

theorem fieldGenerator_four : fieldGenerator ^ 4 = 1 := by
  rw [fieldGenerator, ← map_pow, generatorA_four, map_one]

theorem fieldGenerator_sq_ne_one : fieldGenerator ^ 2 ≠ 1 := by
  intro h
  apply generatorA_sq_ne_one
  apply evenFieldAction_injective
  simpa only [fieldGenerator, map_pow, map_one] using h

/-- Field coordinates of the first concrete generator. -/
theorem generatorA_coordinates (w : hexacode) :
    Hexacode.fieldCoordinates (evenFieldAction generatorA w) =
      ![Hexacode.fieldCoordinates w 0 + Hexacode.fieldCoordinates w 1 +
          Hexacode.fieldCoordinates w 2,
        Hexacode.fieldCoordinates w 0, Hexacode.fieldCoordinates w 1] := by
  have h : ∀ (x : Fin 3 → K) (i : Fin 3),
      orientedLetter (firstThree i)
        (Monomial.act generatorA.val.val (systematicEncoder x) (firstThree i)) =
      ![orientedLetter (firstThree 0) (x 0) + orientedLetter (firstThree 1) (x 1) +
          orientedLetter (firstThree 2) (x 2),
        orientedLetter (firstThree 0) (x 0), orientedLetter (firstThree 1) (x 1)] i := by
    decide +kernel
  funext i
  have hi := h (hexProjection firstThree w) i
  rw [systematic_reconstruct] at hi
  exact hi

/-- Field coordinates of the second concrete generator. -/
theorem generatorB_coordinates (w : hexacode) :
    Hexacode.fieldCoordinates (evenFieldAction generatorB w) =
      ![Hexacode.fieldCoordinates w 2,
        omega * Hexacode.fieldCoordinates w 0,
        omega ^ 2 * Hexacode.fieldCoordinates w 1] := by
  have h : ∀ (x : Fin 3 → K) (i : Fin 3),
      orientedLetter (firstThree i)
        (Monomial.act generatorB.val.val (systematicEncoder x) (firstThree i)) =
      ![orientedLetter (firstThree 2) (x 2),
        omega * orientedLetter (firstThree 0) (x 0),
        omega ^ 2 * orientedLetter (firstThree 1) (x 1)] i := by
    decide +kernel
  funext i
  have hi := h (hexProjection firstThree w) i
  rw [systematic_reconstruct] at hi
  exact hi
end Representation.Hexacode.SixDimensional.EvenImage
