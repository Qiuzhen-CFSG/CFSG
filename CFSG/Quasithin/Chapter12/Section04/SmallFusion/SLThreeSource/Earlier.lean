module

public import CFSG.Quasithin.Chapter12.Section04.SmallFusion.Setup
public import CFSG.Quasithin.Chapter1.Section02.Uniqueness.Source
public import CFSG.Quasithin.ChapterA.Section03.SQTKStructure.NonnormalOrdinary.Source

/-!
# Earlier uniqueness for the original L₃(2) fusion calculation

The completed A.3.8 and A.3.12 source results supply the original uniqueness
interface used by the fixed-line setup. Thus Section 12.4 needs no additional
uniqueness assumption in the known-simple case.

Source: Aschbacher–Smith, 1.2.7, p.506, used in 12.4.5–6, pp.813–814.
-/

public section
namespace CFSG.Quasithin.Chapter12.Section04.SmallFusion.SLThreeSource
universe u

theorem uniquenessEarlier_knownSimple :
    Chapter1.Section02.UniquenessEarlierResults.{u} KnownSimple.IsKnownSimple := by
  refine ⟨?_, ?_, ?_⟩
  · exact Chapter1.Section02.containment_of_theoremsAC
      (fun _ _ _ => ChapterA.Section02.theoremA_knownSimple)
      (fun _ _ _ => ChapterA.Section02.theoremC_knownSimple)
  · intro X _ _ hX hcore B hB
    exact ChapterA.Section03.NonnormalOrdinary.index_and_model_knownSimple hX hcore B hB
  · intro X _ _ hX S
    exact Chapter1.lemma_1_1_4_6 S (hX.evenCharacteristic S)

end CFSG.Quasithin.Chapter12.Section04.SmallFusion.SLThreeSource
