module
public import CFSG.Quasithin.ChapterA.Section03.SQTKStructure.OrdinarySource.Complete
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.SourceModels
public import CFSG.Quasithin.ChapterI.Section03.RankTwoSource.OrbitProjection
/-!
# Complete earlier structure inputs for original I.3.1

The completed A.3.6 covering catalogue supplies every ordinary and noncentral
case. A nonnormal C-component is ordinary, so the complete nonnormal-model
source supplies A.3.8(3) on that original component. The known-simple universal
Theorems A and C discharge both earlier inputs. Together with OrbitProjection,
these are the original hypotheses used in the normal-component lifting theorem.
Source: Aschbacher–Smith, A.3.6–8 and I.3.1, pp.43–46,414–415.
-/
public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterI.RankTwoSource
universe u

theorem earlierA36_knownSimple : EarlierA36 KnownSimple.IsKnownSimple.{u} :=
  ChapterA.SQTKStructure.a36Input_of_theoremsAC
    (fun _ _ _ => ChapterA.Section02.theoremA_knownSimple)
    (fun _ _ _ => ChapterA.Section02.theoremC_knownSimple)

theorem earlierA38_knownSimple : EarlierA38 KnownSimple.IsKnownSimple.{u} := by
  intro X _ _ hX ho B hB
  by_cases hn : B.Normal
  · exact Or.inl hn
  have hq := (ChapterA.Section03.NoncentralNormality.normal_or_quasisimple hX ho hB).resolve_left hn
  exact Or.inr (ChapterA.SQTKStructure.NonnormalOuterSource.nonnormal_component_index_and_model
    (fun _ _ _ => ChapterA.Section02.theoremA_knownSimple)
    (fun _ _ _ => ChapterA.Section02.theoremC_knownSimple) hX ho B ⟨hB.subnormal,hq⟩ hn)
end CFSG.Quasithin.ChapterI.RankTwoSource

