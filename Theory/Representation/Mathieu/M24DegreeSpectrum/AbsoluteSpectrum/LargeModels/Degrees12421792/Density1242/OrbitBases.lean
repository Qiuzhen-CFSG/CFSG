module

public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1242.OrbitBases.Assembly
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1242.OrbitBases.LiteralArithmetic
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1242.OrbitBases.GeneratorLists
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1242.OrbitBases.Certificates.ColumnInverse
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1242.OrbitBases.Certificates.RowInverse
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1242.OrbitBases.Certificates.ColumnSteps
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1242.OrbitBases.Certificates.RowSteps
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1242.OrbitBases.Certificates.FirstTranspose
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1242.OrbitBases.Certificates.SecondTranspose

/-!
# Spanning orbits for the fixed degree-1242 vectors

Both fixed vectors have spanning word orbits under the original ATLAS generators.
Checked earlier-predecessor trees realize every stored basis vector by a word,
and checked left inverses show that these vectors span. The two checked transpose
comparisons identify the column calculations with the original column action;
the row calculations use the original matrices directly.

These identities discharge the two spanning premises of
`Degrees12421792.density1242_of_certificates`, without a kernel or completion
premise. Sources and arithmetic conventions: `OrbitBases/source/README.md` and
`Density1242/source/README.md`; James, J. Algebra 27 (1973), 57–111.
-/

public section
namespace Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1242.OrbitBases

/-- The left word orbit of the fixed column spans the full degree-1242 space. -/
theorem column_span : Submodule.span (ZMod 2) (Set.range columnOrbit) = ⊤ := by
  exact column_span_of_checks ColumnInverse.checked ColumnSteps.checked
    FirstTranspose.matrix_eq SecondTranspose.matrix_eq

/-- The right word orbit of the fixed row spans the full degree-1242 space. -/
theorem row_span : Submodule.span (ZMod 2) (Set.range rowOrbit) = ⊤ := by
  exact row_span_of_checks RowInverse.checked RowSteps.checked

end Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1242.OrbitBases
