module

public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1792.ColumnOrbit.SpanningCriterion
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1792.ColumnOrbit.Spanning.Block00
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1792.ColumnOrbit.Spanning.Block01
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1792.ColumnOrbit.Spanning.Block02
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1792.ColumnOrbit.Spanning.Block03
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1792.ColumnOrbit.Spanning.Block04
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1792.ColumnOrbit.Spanning.Block05
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1792.ColumnOrbit.Spanning.Block06
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1792.ColumnOrbit.Spanning.Block07
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1792.ColumnOrbit.Spanning.Block08
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1792.ColumnOrbit.Spanning.Block09
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1792.ColumnOrbit.Spanning.Block10
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1792.ColumnOrbit.Spanning.Block11
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1792.ColumnOrbit.Spanning.Block12
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1792.ColumnOrbit.Spanning.Block13
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1792.ColumnOrbit.Spanning.Block14
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1792.ColumnOrbit.Spanning.Block15
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1792.ColumnOrbit.Spanning.Block16
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1792.ColumnOrbit.Spanning.Block17
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1792.ColumnOrbit.Spanning.Block18
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1792.ColumnOrbit.Spanning.Block19
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1792.ColumnOrbit.Spanning.Block20
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1792.ColumnOrbit.Spanning.Block21
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1792.ColumnOrbit.Spanning.Block22
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1792.ColumnOrbit.Spanning.Block23
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1792.ColumnOrbit.Spanning.Block24
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1792.ColumnOrbit.Spanning.Block25
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1792.ColumnOrbit.Spanning.Block26
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1792.ColumnOrbit.Spanning.Block27

/-!
# The published degree-1792 columns span

Each of the 1792 standard coordinate vectors is an explicitly kernel-checked XOR
of the fixed candidate columns. Consecutive blocks cover every coordinate, and
`column_span_of_reconstruction` transports their packed arithmetic to the actual
binary submodule. No action, rank, density, or independence hypothesis is used.

Source: ATLAS M24G1-f2r1792B0, with conventions and attribution in
`source/README.md` and `Spanning/source/README.md`. The representation-theoretic
application is James, *The modular characters of the Mathieu groups*,
J. Algebra 27 (1973), 57–111.
-/

@[expose] public section
namespace Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1792

private theorem all_coordinates : ColumnSpanning.Covers 0 1792 :=
  (ColumnSpanning.covers_join 0 64 1728 ColumnSpanning.block00
    (ColumnSpanning.covers_join 64 64 1664 ColumnSpanning.block01
    (ColumnSpanning.covers_join 128 64 1600 ColumnSpanning.block02
    (ColumnSpanning.covers_join 192 64 1536 ColumnSpanning.block03
    (ColumnSpanning.covers_join 256 64 1472 ColumnSpanning.block04
    (ColumnSpanning.covers_join 320 64 1408 ColumnSpanning.block05
    (ColumnSpanning.covers_join 384 64 1344 ColumnSpanning.block06
    (ColumnSpanning.covers_join 448 64 1280 ColumnSpanning.block07
    (ColumnSpanning.covers_join 512 64 1216 ColumnSpanning.block08
    (ColumnSpanning.covers_join 576 64 1152 ColumnSpanning.block09
    (ColumnSpanning.covers_join 640 64 1088 ColumnSpanning.block10
    (ColumnSpanning.covers_join 704 64 1024 ColumnSpanning.block11
    (ColumnSpanning.covers_join 768 64 960 ColumnSpanning.block12
    (ColumnSpanning.covers_join 832 64 896 ColumnSpanning.block13
    (ColumnSpanning.covers_join 896 64 832 ColumnSpanning.block14
    (ColumnSpanning.covers_join 960 64 768 ColumnSpanning.block15
    (ColumnSpanning.covers_join 1024 64 704 ColumnSpanning.block16
    (ColumnSpanning.covers_join 1088 64 640 ColumnSpanning.block17
    (ColumnSpanning.covers_join 1152 64 576 ColumnSpanning.block18
    (ColumnSpanning.covers_join 1216 64 512 ColumnSpanning.block19
    (ColumnSpanning.covers_join 1280 64 448 ColumnSpanning.block20
    (ColumnSpanning.covers_join 1344 64 384 ColumnSpanning.block21
    (ColumnSpanning.covers_join 1408 64 320 ColumnSpanning.block22
    (ColumnSpanning.covers_join 1472 64 256 ColumnSpanning.block23
    (ColumnSpanning.covers_join 1536 64 192 ColumnSpanning.block24
    (ColumnSpanning.covers_join 1600 64 128 ColumnSpanning.block25
    (ColumnSpanning.covers_join 1664 64 64 ColumnSpanning.block26
    ColumnSpanning.block27)))))))))))))))))))))))))))

/-- The fixed published 1792 candidate columns span the full coordinate space. -/
theorem column_span : Submodule.span (ZMod 2) (Set.range ColumnData.column) = ⊤ := by
  apply column_span_of_reconstruction
  intro i
  exact all_coordinates i.val (Nat.zero_le _) i.isLt

end Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1792
