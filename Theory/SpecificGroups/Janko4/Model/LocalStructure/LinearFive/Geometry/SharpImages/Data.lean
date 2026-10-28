module
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.LinearFive.Geometry.SharpImages.Checker
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.ElementaryNormalizerCover.ElementaryBound.Data

@[expose] public section
namespace Janko4.LocalStructure.LinearFive.Geometry.SharpImages
open ElementaryNormalizerCover.ElementaryBound

/-- Vertices of the exceptional elementary group of order sixteen. -/
def keep (v : Fin 192) : Bool := v ∈ ([0, 16, 22, 54, 69, 76, 82, 128, 133, 145, 148, 149, 160, 187, 188, 191] : List (Fin 192))

end Janko4.LocalStructure.LinearFive.Geometry.SharpImages
