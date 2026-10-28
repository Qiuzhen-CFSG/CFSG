module

public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.SmallAmalgams.Goldschmidt.GeometricSourceAssembly
public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.SmallAmalgams.Goldschmidt.G2RadiusTwoRecognition
public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.SmallAmalgams.Goldschmidt.MathieuRadiusThree.Source

/-!
# Marked recognition of the original large cubic amalgams

The canonical labels and radius restriction reduce the actual universal
tree to the G₂ and Mathieu cases. Their compatible endpoint markings and
the normal-base reconstruction retain the overlap map of the original
finite pair. All geometric and recognition premises are discharged.

Source: Goldschmidt, Automorphisms of trivalent graphs (1980),
(6.8)--(6.12); Aschbacher--Smith F.6.18, printed pp.309--310.
-/

public section
namespace CFSG.Quasithin.ChapterF.SourceAssembly.Goldschmidt
universe u

/-- The original marked large-amalgam classification. -/
theorem largeNonabelianMarkedAmalgams : LargeNonabelianMarkedAmalgamInput.{u} :=
  largeNonabelian_of_marked_recognition radiusTwoMarkedInput
    MathieuRadiusThree.radiusThreeMarkedInput

end CFSG.Quasithin.ChapterF.SourceAssembly.Goldschmidt
