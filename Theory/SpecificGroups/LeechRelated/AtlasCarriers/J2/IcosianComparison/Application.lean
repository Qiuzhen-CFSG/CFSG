module

public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.IcosianComparison
public import Theory.SpecificGroups.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Short.LocalA5.SourceConstruction.Geometry.Extension

/-!
# Applying the Hall--Janko comparison to the Leech local A₅

Specialize the existing root-J₂ transport to the equivalence obtained from
the five-relator presentation and a generating pair in the actual icosian
quotient. The fixed `comparison` discharges both presentation exactness and
generation in `exists_a5Placement_of_alignment`. Only the independent alignment
of the cubic, dihedral group and inverter remains for the source assembly.

Source: Aschbacher, *Sporadic Groups* (1994), Lemma 49.5, pp.283–284,
using the D₁₀-centralizer A₅ of Section 47. Both the sign quotient and the
map `icosianProjectiveToCo1` are the original concrete constructions.
-/

public section

open Atlas.Conway
namespace Sporadic.LeechRelated.J2.IcosianComparison
open G2FourModule.Embedding.InnerRealization
open Atlas.G2.ConwayRootFour.Embedding.LeechGeometry
open Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators
open Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.LocalA5.SourceConstruction

/-- The literal Leech consumer with its comparison supplied by the proved assembly. -/
theorem exists_a5Placement_of_generatingPair
    (hp : Function.Injective Presentation.toCarrier)
    (x y : IcosianProjectiveModel) (h : Presentation.Relations x y)
    (hgen : Subgroup.closure ({x, y} : Set IcosianProjectiveModel) = ⊤)
    (L : LongFrame) (g : LeechCentralQuotient) (hg : g ∈ centralizerI)
    (M : RootJ2Marks L (conjugatedRootJ2 (comparisonOfGeneratingPair hp x y h hgen) g)) :
    Nonempty (A5Placement L) :=
  exists_a5Placement_of_rootJ2_alignment L (comparisonOfGeneratingPair hp x y h hgen) g hg M

/-- The certified comparison leaves only the independent root-mark alignment input. -/
theorem exists_a5Placement_of_alignment
    (L : LongFrame) (g : LeechCentralQuotient) (hg : g ∈ centralizerI)
    (M : RootJ2Marks L (conjugatedRootJ2 comparison g)) :
    Nonempty (A5Placement L) :=
  exists_a5Placement_of_rootJ2_alignment L comparison g hg M

end Sporadic.LeechRelated.J2.IcosianComparison
