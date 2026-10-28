module

public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.SmallAmalgams.Goldschmidt.SourceReconstruction
public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.SmallAmalgams.Goldschmidt.GeometricSourceAssembly
public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.SmallAmalgams.Goldschmidt.MathieuRadiusThree.Source
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.Semilinear.Recognition.FSource.LargeNonabelianSourceAssembly
public import CFSG.Quasithin.ChapterA.Section02.SourceAssembly.Complete

/-!
# The corrected F.6 consumer of the independent Gol80 source arguments

The proved Theorems A and C discharge the earlier classification premises.
The four arguments in the original interface concern the infinite universal tree
and its marked two-perfect base. Reconstruction of the finite local pair is
supplied by the proved normal-base extension theorems in either orientation.
The original four-input interface is preserved. The final specialization
uses the proved canonical labels, radius restriction and Mathieu relations,
retaining only the radius-two marked recognition and the Mathieu endpoint
group recognition. These supply the exact corrected F.6 interface consumed
by Chapters 14 and 15.

Source: Goldschmidt (1980), Sections 3--6; Aschbacher--Smith F.6.18,
printed pp.309--310.
-/

public section
namespace CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.Semilinear.Recognition.FSource
open ChapterF.SourceAssembly.Goldschmidt
universe u

/-- Conditional source assembly with genuine A/C and normal-base reconstruction
already discharged. The four Gol80 source arguments remain explicit. -/
theorem sourceClassification_knownSimple_of_source_cuts
    (labels : CanonicalLabelsInput.{u}) (radius : CanonicalRadiusInput.{u})
    (two : RadiusTwoMarkedInput.{u}) (three : RadiusThreeMarkedInput.{u}) :
    SourceClassificationInput KnownSimple.IsKnownSimple.{u} :=
  sourceClassificationInput_of_large_nonabelian_marked_amalgams
    (fun _ _ _ => ChapterA.Section02.theoremA_knownSimple)
    (fun _ _ _ => ChapterA.Section02.theoremC_knownSimple)
    (largeNonabelian_of_geometric_source_cuts labels radius two three)

/-- The corrected F.6 source implication after the tree geometry and the
Mathieu local relations are proved. Only the two endpoint-recognition
arguments remain. -/
theorem sourceClassification_knownSimple_of_remaining_recognition
    (two : RadiusTwoMarkedInput.{u})
    (groups : MathieuRadiusThree.LocalGroupsInput.{u}) :
    SourceClassificationInput KnownSimple.IsKnownSimple.{u} :=
  sourceClassificationInput_of_large_nonabelian_marked_amalgams
    (fun _ _ _ => ChapterA.Section02.theoremA_knownSimple)
    (fun _ _ _ => ChapterA.Section02.theoremC_knownSimple)
    (largeNonabelian_of_marked_recognition two
      (MathieuRadiusThree.radiusThreeMarkedInput_of_local_groups groups))

end CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.Semilinear.Recognition.FSource
