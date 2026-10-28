module
public import CFSG.Quasithin.Chapter10.SourceA5ModuleSymplecticExceptions
public import CFSG.Quasithin.Chapter3.Section01.SourceE213RecognizedPair
/-!
# A recognized E.2.7 pair in the original A5 module-selection action

The actual fundamental setup supplies the source qrc input. A recognized
pair on its literal intrinsic H-module therefore proves the original local
module cubic bound. The pair's coefficient field may be a proper subfield;
the module, local join, quotient action and selected H are unchanged.

Source: Aschbacher--Smith E.2.7--13 and the local-module application
3.1.6 and 3.2.5--6, printed pp.219--225,573--581.
-/
public section
open Subgroup Theory.GroupTheory Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter10
open Chapter3.Section02 ChapterD ChapterD.UniqueFactor
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)

/-- Literal source consumer of E.2.7 recognized pair data. -/
theorem source_localModule_cubic_bound_of_recognized_pair
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G) D.maximalLocal)
    (hout : ¬ D.moduleSubgroup ≤ H.pCoreIn 2)
    (hp : ChapterB.IsMinimalParabolicOver (T.subtype hH.1.1.2) ⊤)
    (hr : ChapterE.Witnesses.SymplecticFour.HasRecognizedPair
      (T.subtype hH.1.1.2)
      (ChapterB.minimalParabolicMax (T.subtype hH.1.1.2) hp)
      (D.moduleSubgroup.subgroupOf H)) :
    SourceLocalModuleCubicBound D := by
  apply source_localModule_cubic_bound_of_image D
  exact (D.qrcHypotheses (source_module_nonsolvable_uniqueness D) hH).cubicRatio_le_two_of_recognized_pair
    D.simpleQTKE
    (D.lemma_3_2_3_uniqueness (source_module_nonsolvable_uniqueness D)).1 hout hp hr

/-- Literal source consumer of recognition through the full H maximal core. -/
theorem source_localModule_cubic_bound_of_recognized_star
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G) D.maximalLocal)
    (hout : ¬ D.moduleSubgroup ≤ H.pCoreIn 2)
    (hp : ChapterB.IsMinimalParabolicOver (T.subtype hH.1.1.2) ⊤)
    (hr : let S := T.subtype hH.1.1.2
      let q := QuotientGroup.mk' (ChapterB.minimalParabolicCore S hp)
      ChapterE.Witnesses.SymplecticFour.HasRecognizedPair
        (S.mapSurjective (QuotientGroup.mk'_surjective _))
        ((ChapterB.minimalParabolicMax S hp).map q)
        ((D.moduleSubgroup.subgroupOf H).map q)) :
    SourceLocalModuleCubicBound D := by
  apply source_localModule_cubic_bound_of_image D
  exact (D.qrcHypotheses (source_module_nonsolvable_uniqueness D) hH).cubicRatio_le_two_of_recognized_star
    D.simpleQTKE
    (D.lemma_3_2_3_uniqueness (source_module_nonsolvable_uniqueness D)).1 hout hp hr

end CFSG.Quasithin.Chapter10
