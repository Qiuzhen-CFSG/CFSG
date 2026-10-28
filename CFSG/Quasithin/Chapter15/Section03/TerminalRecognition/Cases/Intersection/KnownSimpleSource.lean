module

public import CFSG.Quasithin.Chapter15.Section03.TerminalRecognition.Cases.Intersection.SourceClassifications
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.TwoFactors.FFBranch.Recognition.ClassificationComparison.SourceB5.Complete

/-!
# The proved B.5 source input for the terminal intersection

The terminal consumer already allows the actual outer A₆--C₃ group shape
instead of the disputed representation splitting. Thus the proved adequate
B.5 classification supplies its complete source input directly: every other
constructor retains the same action data, and the outer constructor uses
the existing group-shape alternative on the same actor.

Source: Aschbacher--Smith B.5.6, applied in the final proof of 15.3.1,
printed p.1155.
-/

public section
namespace CFSG.Quasithin.Chapter15.Section03.TerminalRecognition.Intersection
open CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison
universe u v

theorem sourceFFClassification_knownSimple :
    SourceFFClassificationInput.{u,v} KnownSimple.IsKnownSimple := by
  intro D _ _ W _ _ ρ h
  have ha := FFAlternatives.SourceB5.classification.general D W ρ h
  cases ha with
  | trivial ht => exact Or.inl (.trivial ht)
  | quasisimple hq hc => exact Or.inl (.quasisimple hq hc)
  | symmetricThree hs => exact Or.inl (.symmetricThree hs)
  | twoFactors hp => exact Or.inl (.twoFactors hp)
  | outerSixThree hs => exact Or.inr ⟨hs⟩
  | hyperplane hh => exact Or.inl (.hyperplane hh)

end CFSG.Quasithin.Chapter15.Section03.TerminalRecognition.Intersection
