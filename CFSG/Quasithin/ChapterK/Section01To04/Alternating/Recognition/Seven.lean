module

public import CFSG.Quasithin.ChapterK.Section01To04.Alternating.Recognition.Seven.Inputs
public import CFSG.Quasithin.ChapterK.Section01To04.Alternating.Recognition.Seven.NaturalExtension
public import CFSG.Quasithin.ChapterK.Section01To04.Alternating.Recognition.Seven.EightExclusion
public import CFSG.Quasithin.ChapterK.Section01To04.Alternating.Recognition.Seven.Degree
public import CFSG.Quasithin.ChapterK.Section01To04.Alternating.Recognition.Seven.FourSpace
public import CFSG.Quasithin.ChapterK.Section01To04.Alternating.Recognition.Seven.SixSpace

/-!
# Assembling the A₇ representation branch of K.1

The degree bound reduces the representation problem to dimensions four and six.
The four-space input gives the actual restricted SL₄(2) model and G = L. In
dimension six, the natural normalizer theorem supplies the permitted marked
S₇ extension after the restricted module has been recognized.

The proved degree and fixed-dimension recognition results discharge all three
inputs in `sevenRecognition`. The conditional assembly remains available
separately. The imported eight-space exclusion proves the source reason for
rejecting that GM02 row: its restriction to the actual component is reducible.

Source: Aschbacher–Smith, K.1.2, printed p.452 (PDF p.463).
-/

public section

namespace CFSG.Quasithin.ChapterK.Alternating
open RecognitionInputs

universe u v

/-- Assemble the A₇ branch from the numerical bound and the two fixed-degree
recognition results. The natural ambient extension is discharged here. -/
theorem sevenRecognition_of_dimension_branches
    (hd : Seven.DegreeBound.{u,v}) (h4 : Seven.FourSpace.{u,v})
    (h6 : Seven.SixSpace.{u,v}) : SevenRecognition.{u,v} := by
  intro G V _ _ _ _ _ ρ K L h eL
  rcases hd ρ K L h eL with hd | hd
  · exact Or.inr (h4 ρ K L h eL hd)
  · obtain ⟨e⟩ := h6 ρ K L h eL hd
    exact Or.inl (sevenNaturalAction_of_restriction ρ L h e)

/-- The A₇ representation alternatives in K.1.2: the natural six-space with
its permitted marked S₇ extension, or the actual restricted SL₄(2) four-space
with ambient actor equal to the component. No degree or recognition premise
remains beyond the original source input. -/
theorem sevenRecognition : SevenRecognition.{u,v} :=
  sevenRecognition_of_dimension_branches sevenDegreeBound sevenFourSpace sevenSixSpace

end CFSG.Quasithin.ChapterK.Alternating
