module

public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degree220Pair.Realization
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degree220Pair.Density.First
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degree220Pair.Density.Second

/-!
# The two concrete degree-220 pairs generate full matrix algebras

For each published ATLAS pair, a short algebra expression has a checked cyclic
basis and two null vectors. The cyclic-centralizer argument places their
rank-one outer product in the generated algebra. Checked left and right
orbit bases then span every matrix. All calculations use kernel-certified
binary arithmetic, with transposition preserving the literal exported
column-action convention. Native M24 realization is an independent obligation.

Sources: James, J. Algebra 27 (1973), 57–111, and the ATLAS files attributed
in Degree220Pair/source/README.md. Witness reproduction and the full-product
benchmark are recorded in Density/source/README.md.
-/

public section
namespace Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degree220Pair

/-- Both literal published pairs generate the entire 220-by-220 matrix algebra. -/
theorem matrixAlgebrasFull : MatrixAlgebrasFull := by
  intro second
  cases second
  · exact Density.first_full
  · exact Density.second_full

end Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degree220Pair
