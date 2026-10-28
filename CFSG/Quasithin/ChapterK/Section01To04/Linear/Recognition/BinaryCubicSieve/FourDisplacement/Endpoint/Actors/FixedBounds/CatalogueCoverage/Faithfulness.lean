module

public import CFSG.Quasithin.ChapterK.Section01To04.Linear.Recognition.BinaryCubicSieve.FourDisplacement.Endpoint.Actors.FixedBounds.CatalogueCoverage.Code

/-!
# Faithfulness of the 128 adjoint actor codes

Seven entries of the fourteen-dimensional quotient matrix distinguish all
codes. An explicit inverse for the packed seven-bit signature is checked by
kernel reduction. Equality of actual actors implies equality of coordinate
operators, so the check proves injectivity of `codeActor` on the literal
adjoint quotient, without any hypothesis on representation faithfulness.

Source application: Guralnick–Malle Lemma 4.5 and Proposition 4.8 step 3A;
Aschbacher–Smith K.3.2, printed pp.454–455.
-/

public section
set_option backward.isDefEq.respectTransparency false
open Representation Representation.BinaryOffender
namespace CFSG.Quasithin.ChapterK.Linear.Recognition.BinaryCubicSieve.FourDisplacement.Endpoint.FixedBounds

@[simp] theorem codeActor_zero : codeActor 0 = 1 := by
  have hu : upperElement (codeBits 0) = 1 := by
    apply Subtype.ext
    change upperMatrix (codeBits 0) = 1
    decide +kernel
  simp [codeActor, codeOuter, hu]

private def fingerprint (c : Code) : Code :=
  Fin.ofNat 128 (1 * (actMatrix c 0 0).val +
    2 * (actMatrix c 0 7).val +
    4 * (actMatrix c 0 12).val +
    8 * (actMatrix c 2 12).val +
    16 * (actMatrix c 3 9).val +
    32 * (actMatrix c 4 7).val +
    64 * (actMatrix c 5 4).val)

private def fingerprintInverse : Code → Code :=
  ![1, 0, 5, 4, 3, 2, 7, 6, 9, 8, 13, 12, 11, 10, 15, 14,
    33, 32, 37, 36, 43, 42, 47, 46, 41, 40, 45, 44, 35, 34, 39, 38,
    17, 16, 21, 20, 19, 18, 23, 22, 25, 24, 29, 28, 27, 26, 31, 30,
    49, 48, 53, 52, 59, 58, 63, 62, 57, 56, 61, 60, 51, 50, 55, 54,
    65, 64, 69, 68, 67, 66, 71, 70, 73, 72, 77, 76, 75, 74, 79, 78,
    97, 96, 101, 100, 107, 106, 111, 110, 105, 104, 109, 108, 99, 98, 103, 102,
    81, 80, 85, 84, 91, 90, 95, 94, 89, 88, 93, 92, 83, 82, 87, 86,
    113, 112, 117, 116, 115, 114, 119, 118, 121, 120, 125, 124, 123, 122, 127, 126]

private theorem fingerprint_leftInverse : ∀ c, fingerprintInverse (fingerprint c) = c := by
  decide +kernel

/-- Seven entries of the literal quotient action distinguish all actor codes. -/
theorem codeActor_injective : Function.Injective codeActor := by
  intro a b hab
  have hm : actMatrix a = actMatrix b := by
    rw [← coordinateAction_matrix, ← coordinateAction_matrix]
    congr 1
    unfold coordinateAction
    rw [hab]
  have hs : fingerprint a = fingerprint b := by simp only [fingerprint, hm]
  have he := congrArg fingerprintInverse hs
  simpa only [fingerprint_leftInverse] using he

end CFSG.Quasithin.ChapterK.Linear.Recognition.BinaryCubicSieve.FourDisplacement.Endpoint.FixedBounds
