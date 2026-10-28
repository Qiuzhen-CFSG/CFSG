module

public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.SmallAmalgams.Goldschmidt.Complete
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.Semilinear.Recognition.FSource.SourceCutAssembly

/-!
# The corrected F.6 classification for the full known-simple class

The proved marked large-amalgam theorem supplies the final geometric input.
Theorems A and C already hold for the full known-simple catalogue, so the
actual source classification has no remaining recognition premise.

Source: Aschbacher--Smith F.6.18, printed pp.309--310.
-/

public section
namespace CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.Semilinear.Recognition.FSource
universe u

/-- Corrected source F.6, with all classification and recognition inputs proved. -/
theorem sourceClassification_knownSimple_complete :
    SourceClassificationInput KnownSimple.IsKnownSimple.{u} :=
  sourceClassificationInput_of_large_nonabelian_marked_amalgams
    (fun _ _ _ => ChapterA.Section02.theoremA_knownSimple)
    (fun _ _ _ => ChapterA.Section02.theoremC_knownSimple)
    ChapterF.SourceAssembly.Goldschmidt.largeNonabelianMarkedAmalgams

end CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.Semilinear.Recognition.FSource
