module

public import CFSG.Quasithin.ChapterG.Section01.SL2FourRecognition

/-!
# The universal projective recognition implication over F₄

The concrete root-space proof of G.1.3 applies to every finite binary
SL₂(F₄)-module and every projective map satisfying the source criterion.
This module exposes that theorem in the exact universal interface consumed
by the A₅ branch of G.2.4. The resulting coordinates intertwine the original
action with the natural matrix action; multiplicity zero is included.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
G.1.1 and G.1.3, printed p.327.
-/

public section

namespace CFSG.Quasithin.ChapterG.Section01.SL2FourRecognition
open Section02.AlternatingFive.Recognition
open ProjectiveGeometry

universe u

/-- The full universal G.1.3 implication required by the literal G.2.4
upper quotient, proved from its projective hypotheses. -/
theorem recognitionInput : RecognitionInput.{0,u} F4 := by
  intro M _ _ _ σ φ h
  exact naturalCopies h

end CFSG.Quasithin.ChapterG.Section01.SL2FourRecognition
