module
public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.SmallAmalgams.Goldschmidt.CanonicalLabelsAssembly
public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.SmallAmalgams.Goldschmidt.OddCanonicalRadius.Source

/-!
# Marked classification after both source geometric arguments

Goldschmidt's canonical labels and radius restriction now follow from the
actual two-perfect universal tree action. The only remaining source arguments
are the compatible G₂ and Mathieu marked recognitions at radii two and three.
The original finite amalgam is then recovered by the proved normal-base
reconstruction, retaining its common overlap map.

Source: Goldschmidt, *Automorphisms of trivalent graphs* (1980),
(6.8)--(6.12), printed pp.399--406.
-/

public section
namespace CFSG.Quasithin.ChapterF.SourceAssembly.Goldschmidt
universe u

/-- The actual large F.6 source input with both geometric arguments proved.
Only the two compatible marked recognitions remain. -/
theorem largeNonabelian_of_marked_recognition
    (two : RadiusTwoMarkedInput.{u}) (three : RadiusThreeMarkedInput.{u}) :
    LargeNonabelianMarkedAmalgamInput.{u} :=
  largeNonabelian_of_radius_and_marked_recognition canonicalRadius two three

end CFSG.Quasithin.ChapterF.SourceAssembly.Goldschmidt
