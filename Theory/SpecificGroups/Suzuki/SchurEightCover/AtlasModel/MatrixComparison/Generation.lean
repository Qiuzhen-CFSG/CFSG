module

public import Theory.SpecificGroups.Suzuki.SchurEightCover.AtlasModel.MatrixComparison.NativeEmbedding
public import Theory.SpecificGroups.Suzuki.SchurEightCover.AtlasModel.MatrixComparison.Generation.ReverseWords
public import Theory.SpecificGroups.Suzuki.SchurEightCover.AtlasModel.MatrixComparison.Generation.Arithmetic

/-!
# The displayed pair generates the literal native Suzuki group

The checked reverse words recover root(1,0), torus(v), and Weyl from the
pair. Torus conjugation, root squaring, and finite field coverage then
recover every root and every torus in the native definition. Entrywise
field transport therefore makes the published native embedding surjective.

This supplies the generation premise of `nativeEquivOfSurjective` and
`equivOfComparisons`, independently of the degree-65 action comparison.
Source context: Aschbacher–Smith I.1.1 and I.1.3(5), printed p.407;
see `AtlasModel/source/README.md` for numerical attribution.
-/

public section
namespace BenderSuzuki.MatrixGroups.SchurEightCover.AtlasModel.MatrixComparison.Generation

/-- The explicit ATLAS matrix pair generates all of the native Sz(8). -/
theorem nativeEmbedding_surjective : Function.Surjective nativeEmbedding := by
  intro g
  obtain ⟨a, ha, hea⟩ := Subgroup.mem_map.mp (native_le_triple_map g.property)
  refine ⟨⟨a, tripleSubgroup_le_pair ha⟩, ?_⟩
  exact Subtype.ext hea

end BenderSuzuki.MatrixGroups.SchurEightCover.AtlasModel.MatrixComparison.Generation
