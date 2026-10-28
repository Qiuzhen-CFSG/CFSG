module
public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.SmallAmalgams.Goldschmidt.CanonicalLabelsSource
public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.SmallAmalgams.Goldschmidt.SourceReconstruction

/-!
# Marked source assembly with canonical labels discharged

The original large universal residual action supplies its canonical labels
by the full source (6.4)--(6.8) construction. The only remaining marked
classification arguments are the radius restriction and the two compatible
model recognitions. Normal-base reconstruction retains the original overlap
maps and is already proved.

Source: Goldschmidt (1980), Sections 5--6, pp.395--406.
-/

public section
namespace CFSG.Quasithin.ChapterF.SourceAssembly.Goldschmidt
universe u

/-- The actual large F.6 marked-amalgam input with the canonical-label source
premise proved. The radius and both marked recognitions remain explicit. -/
theorem largeNonabelian_of_radius_and_marked_recognition
    (radius : CanonicalRadiusInput.{u}) (two : RadiusTwoMarkedInput.{u})
    (three : RadiusThreeMarkedInput.{u}) : LargeNonabelianMarkedAmalgamInput.{u} :=
  largeNonabelian_of_geometric_source_cuts canonicalLabelsInput radius two three

end CFSG.Quasithin.ChapterF.SourceAssembly.Goldschmidt
