module

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.SourceRankOne.OriginalSource.AssemblyFixedLine
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.SourceSetup

/-!
# Original 15.3.25 from the classified small source

The small branch of the rank-one exclusion consumes the actual C.1.32/C.1.34
and B.5 source classifications through `SourceData.markedMS`.  Its surviving
small cases are exactly the A₆, G₂ and binary-linear alternatives, and
`source_small_false_of_MS_cases` excludes each of them with the original
marked module.  The middle branch is already discharged by the fixed-line
residual identity; its terminal contradiction is the paired end-node geometry
of `EndNodeData.false_of_fixedLineResidual`.

No replacement rank tuple or abstract paired configuration is added here: all
subgroups, quotient maps and markings are those of the original 15.3 source.
The two universal classifications remain explicit inputs, as they are in the
source theorem's preceding C.1.32/C.1.34 applications.

Source: Aschbacher–Smith, C.1.30–34 and 15.3.25–32, printed pp.1130–1134.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.SourceRankOne.OriginalSource
open ChapterA.Section05To06 RankOneConfiguration SmallExtension
open SmallExtension.MarkedMS
open Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison.FFAlternatives
universe u
variable {G : Type u} [Group G] [Finite G]

/-- The original 15.3.25 exclusion after applying the authorized small-source
classifications.  The middle/fixed-line and paired branches are internal; no
small-core case callback remains. -/
theorem source_lemma_15_3_25_of_classifications
    (earlier : EarlierMSClassifications.{u} KnownSimple.IsKnownSimple)
    (ff : ProjectiveLine.CompleteClassificationInput.{u,u} KnownSimple.IsKnownSimple)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (d : LocalData G)
    (hempty : MainForward.faithfulLocalComponents d.T = ∅)
    (hM : IsOrderingMaximal d.T d.M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions d.T : Set G)) = {d.Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (d.T : Subgroup G)).ncard)
    (hshadow : SymmetricThreeShadow d.Yplus d.S) :
    ∀ I ∈ d.Hplus, generalizedFitting I ≠ pCore 2 I := by
  apply source_not_characteristicTwo_of_branches hG d hempty hM hu hmany hshadow
  · intro I c s hm
    exact source_small_false_of_MS_cases s hm
      (s.markedMS earlier ff hm).cases (s.markedMS earlier ff hm).simple
  · intro I c e mark
    exact source_lemma_15_3_32_3 hG d hempty hM hu hmany hshadow
      e.source.minimal e.source.characteristicTwo c mark

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.SourceRankOne.OriginalSource
