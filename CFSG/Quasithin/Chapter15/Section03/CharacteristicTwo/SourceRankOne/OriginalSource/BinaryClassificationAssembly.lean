module

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.LinearThree.Assembly
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.LinearThree.DistanceEightDisplacement
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.SourceRankOne.OriginalSource.MSAssembly

/-!
# The original rank-one exclusion from binary MS classification

The full earlier linear-three implication reduces to the field with two
elements, because the original small central-core quotient forces that field.
The existing source assembly then excludes the actual local components of
15.3.25. Its original Sylow subgroups, module actions and residual choices are
unchanged. Both independent classifications below remain explicit premises;
this theorem does not assert their exhaustiveness.

Source: Aschbacher--Smith C.1.32, C.1.34 and 15.3.25--32,
printed pp.135--137 and 1130--1134.
-/

public section
open Subgroup Theory.GroupTheory
open CFSG.Quasithin.Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.SourceRankOne.OriginalSource
open ChapterA.Section05To06 RankOneConfiguration SmallExtension SmallExtension.MarkedMS
universe u
variable {G : Type u} [Group G] [Finite G]

/-- A literal original-source consumer of the binary reduction, retaining
the two independent earlier source implications as its only MS premises. -/
theorem source_lemma_15_3_25_of_binary_MS_classification
    (rankTwo : ∀ (J : Type u) [Group J] [Finite J] (L R : Subgroup J),
      SmallMSPair KnownSimple.IsKnownSimple L R → RankTwoAlternatives L R)
    (binary : ∀ (J : Type u) [Group J] [Finite J] (L R : Subgroup J),
      SmallMSPair KnownSimple.IsKnownSimple L R →
      Nonempty ((L ⧸ pCore 2 L) ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) →
      ∀ S : Subgroup J, Chapter1.IsSylowIn 2 S (L ⊔ R) → R ≤ S →
        ∃ e : (L ⧸ pCore 2 L) ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2),
          MSModuleAlternatives L R S 1 (ZMod 2) e)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (d : LocalData G)
    (hempty : MainForward.faithfulLocalComponents d.T = ∅)
    (hM : IsOrderingMaximal d.T d.M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions d.T : Set G)) = {d.Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (d.T : Subgroup G)).ncard)
    (hshadow : SymmetricThreeShadow d.Yplus d.S) :
    ∀ I ∈ d.Hplus, generalizedFitting I ≠ pCore 2 I :=
  source_lemma_15_3_25_of_MS_classifications
    (EarlierMSClassifications.of_binary rankTwo binary) hG d hempty hM hu hmany hshadow

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.SourceRankOne.OriginalSource
