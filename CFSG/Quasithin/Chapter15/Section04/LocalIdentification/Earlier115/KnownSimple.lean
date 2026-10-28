module
public import CFSG.Quasithin.ChapterA.Section02.SourceAssembly.Complete
public import CFSG.Quasithin.Chapter15.Section04.LocalIdentification.Earlier115
/-!
# The source 1.1.5 input to Chapter 15 with A/B/C discharged

The original ambient hypotheses now supply the Chapter 15 Earlier115 package
for the full known-simple catalogue, through the unconditional A.2 induction.
Source: Aschbacher--Smith 1.1.5 and 15.3--4.
-/
public section
namespace CFSG.Quasithin
open ChapterA.Section02
universe u
variable {G : Type u} [Group G] [Finite G]
theorem Chapter15.Section04.SourceRecognition.Source.earlier115Three_knownSimple :
    Chapter15.Section03.Candidates.ComponentStructure.Earlier115Three KnownSimple.IsKnownSimple G :=
  Chapter15.Section04.SourceRecognition.Source.earlier115Three
    (fun X _ _ => theoremsABC_knownSimple (G := X))

theorem Chapter15.Section04.SourceRecognition.Source.earlier115_knownSimple
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) :
    Chapter15.Section04.SourceRecognition.Source.Earlier115 (G := G) :=
  Chapter15.Section04.SourceRecognition.Source.earlier115 hG
    (fun X _ _ => theoremsABC_knownSimple (G := X))
end CFSG.Quasithin
