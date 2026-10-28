module

public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.SourceAssembly.OriginalGeometry
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.LineNormalizers.PreDescentSource.Fusion
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.Semilinear.Recognition.FSource.SourceCutAssembly
public import CFSG.Quasithin.Chapter15.Section04.Centralizer.InitialSource.KnownSimple.NoncentralSource
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.SourceRankOne.OriginalSource.BinaryLargeCenter
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearThree.OriginalSource.FixedFourRadical
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearThree.OriginalSource.FixedFourElementary
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearThree.OriginalSource.FixedFourPlane
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearThree.OriginalSource.IntrinsicFour
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.SourceRankOne.OriginalSource.BinarySwitching
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.SourceRankOne.OriginalSource.BinarySmallDisplacement

/-!
# Original Theorem E consumers of the remaining marked recognition

The corrected F.6 source classification now follows from two precise
recognition arguments: the radius-two G₂ marking and the radius-three Mathieu
endpoint groups. Canonical labels, the radius restriction, the Mathieu local
relations, normal-base reconstruction and Theorems A and C are proved inputs.

Apply this classification to the original final contradiction in §15.3 and
the many-centralizer-overgroups branch in §15.4. The former retains exactly
its earlier local data and the original centralizer and normalizer bounds;
the latter requires no additional earlier source premise.

The separate original-fusion specialization also supplies the normalizer
bound from the centralizer condition already present in its fusion record,
and uses the complete corrected F.6 theorem. It retains only the original
earlier local data, fusion inputs and simple-QTKE hypothesis.

The large-distance source31 application constructs the natural coefficient
model on the whole component-core center, retaining its component-central
kernel. It identifies the literal first fixed line as both [V₁,Q] and
C_ZS(L). The small-displacement theorem on the entire commutator core then
excludes the original large binary branch. The complete binary-row consumer
retains only prescribed critical-path replacement; the original-core-action
premise is discharged.

For the rank-two source, the actual MS93 four-group is the third commutator
of the component's commutator core. This characteristic description identifies
its original image with the complementary plane [V,Y_C], proves fixation by
the original radical, and places V inside the commutator core. These conclusions
require no bound on the full fixed factor. Prescribed replacement and fixation
by the larger original two-core remain source obligations.

Source: Aschbacher--Smith, F.6.18, the final proof of 15.3.1 and §15.4;
Goldschmidt (1980), (6.12).
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter15
open ChapterF.SourceAssembly.Goldschmidt
universe u
variable {G : Type u} [Group G] [Finite G]

namespace Section03.AbelianAmalgam.GoldschmidtCore.Centrality.SourceAssembly
open Semilinear

/-- The original terminal contradiction with corrected F.6 reduced to its
two remaining recognition arguments. -/
theorem terminal_contradiction_knownSimple_from_remaining_recognition
    (two : RadiusTwoMarkedInput.{u})
    (groups : MathieuRadiusThree.LocalGroupsInput.{u})
    {T : Sylow 2 G} {M Mc P E : Subgroup G}
    (earlier : LocalStructure.EarlierData T M Mc P E)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hfixed : centralizer (fixedPlane P (planeStabilizer T P) : Set G) ≤ M)
    (hZ : Nat.Coprime 3 (Nat.card (normalizer
      (fixedPlane (localModule T M) (planeStabilizer T P) : Set G)))) : False :=
  terminal_contradiction_knownSimple_from_original_bounds earlier hG hfixed hZ
    (Recognition.FSource.sourceClassification_knownSimple_of_remaining_recognition two groups)

end Section03.AbelianAmalgam.GoldschmidtCore.Centrality.SourceAssembly

namespace Section04.InitialSource.KnownSimpleSource
open Section03.AbelianAmalgam.GoldschmidtCore.Centrality.Semilinear.Recognition

/-- The many-centralizer-overgroups branch of Theorem E from the original
ambient hypotheses and the two remaining F.6 recognition arguments. -/
theorem source_many_theoremE_from_remaining_recognition
    (two : RadiusTwoMarkedInput.{u})
    (groups : MathieuRadiusThree.LocalGroupsInput.{u})
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    (hmany : 1 < (maximalTwoLocalOvergroups
      (centralizer (omegaOneCenterAmbient (T : Subgroup G) : Set G))).ncard) :
    ClassificationModels.IsTheoremEModel G :=
  source_many_theoremE_from_f_source
    (FSource.sourceClassification_knownSimple_of_remaining_recognition two groups)
    hG T hempty hmany

end Section04.InitialSource.KnownSimpleSource
end CFSG.Quasithin.Chapter15
