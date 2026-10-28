module

public import CFSG.Quasithin.ChapterA.Section01.SectionRank.ThreeReducibility
public import CFSG.Quasithin.ChapterG.Section09.FittingRecognition.Preparation

/-!
# The genuine A.1.31(3) input for degree-six recognition

The literal source-cover theorem supplies the existing preparation input.
No rank assertion is transferred to a quotient: the rank bound remains on
D in the same displayed surjection used by the G.9.4 consumer.

Source: Aschbacher--Smith, A.1.31(3), printed pp.27--28, as used in G.9.4.
-/

public section
namespace CFSG.Quasithin.ChapterG.Section09.FittingRecognition

/-- The cubic reducibility input of the actual G.9.4 preparation is proved
by A.1.31(3), with its original cover and no additional assumptions. -/
theorem threeSectionReducibilityInput : ThreeSectionReducibilityInput := by
  intro D E _ _ _ _ f hf hrank hF hEA hcard hr2
  exact ChapterA.lemma_A_1_31_3_of_surjective f hf hrank hF hEA hcard hr2

end CFSG.Quasithin.ChapterG.Section09.FittingRecognition
