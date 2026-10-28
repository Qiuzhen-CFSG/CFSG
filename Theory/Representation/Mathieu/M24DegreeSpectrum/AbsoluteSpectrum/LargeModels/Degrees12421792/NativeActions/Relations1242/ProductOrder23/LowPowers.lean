module

public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1242.ProductOrder23.LowPowers.Block00
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1242.ProductOrder23.LowPowers.Block01
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1242.ProductOrder23.LowPowers.Block02
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1242.ProductOrder23.LowPowers.Block03
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1242.ProductOrder23.LowPowers.Block04
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1242.ProductOrder23.LowPowers.Block05
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1242.ProductOrder23.LowPowers.Block06
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1242.ProductOrder23.LowPowers.Block07
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1242.ProductOrder23.LowPowers.Block08
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1242.ProductOrder23.LowPowers.Block09
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1242.ProductOrder23.LowPowers.Block10
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1242.ProductOrder23.LowPowers.Block11
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1242.ProductOrder23.LowPowers.Block12
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1242.ProductOrder23.LowPowers.Block13
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1242.ProductOrder23.LowPowers.Block14
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1242.ProductOrder23.LowPowers.Block15
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1242.ProductOrder23.LowPowers.Block16
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1242.ProductOrder23.LowPowers.Block17
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1242.ProductOrder23.LowPowers.Block18
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1242.ProductOrder23.LowPowers.Block19
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1242.ProductOrder23.LowPowers.Block20
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1242.ProductOrder23.LowPowers.Block21
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1242.ProductOrder23.LowPowers.Block22
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1242.ProductOrder23.FirstProduct

/-!
# The square and cube of the literal degree-1242 generator product

Bounded row certificates prove the two literal products `c1 * c1 = c2` and
`c2 * c1 = c3`. A single independently checked base-2048 expansion table for
the common right operand supplies the carry-free checker. Its radix exceeds
1242, so no column sum carries. Sparse row hints are checked as well.

Together with `first_product`, these identities identify powers two and three
of the original untransposed ATLAS product. They discharge exactly h2 and h3
of `Relations1242.product_order23_of_products` and `product_word2_of_products`;
the remaining four products belong to the parent assembly's other producers.
Source: M24G1-f2r1242B0.m1/.m2 and M24G1-P1, word 2;
see `LowPowers/source/README.md`.
-/

public section
namespace Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1242.ProductOrder23
open Relations1792.Arithmetic
namespace LowPowers
open Tables

theorem wide_correct : wideChunks.flatten = c1Rows.map (expandBlocks 18 69) := by
  simp only [wideChunks, c1Rows, c1Chunks, List.flatten_cons, List.flatten_nil,
    List.map_append, List.map_nil,
    ← Block00.wide_correct,
    ← Block01.wide_correct,
    ← Block02.wide_correct,
    ← Block03.wide_correct,
    ← Block04.wide_correct,
    ← Block05.wide_correct,
    ← Block06.wide_correct,
    ← Block07.wide_correct,
    ← Block08.wide_correct,
    ← Block09.wide_correct,
    ← Block10.wide_correct,
    ← Block11.wide_correct,
    ← Block12.wide_correct,
    ← Block13.wide_correct,
    ← Block14.wide_correct,
    ← Block15.wide_correct,
    ← Block16.wide_correct,
    ← Block17.wide_correct,
    ← Block18.wide_correct,
    ← Block19.wide_correct,
    ← Block20.wide_correct,
    ← Block21.wide_correct,
    ← Block22.wide_correct]

private def squareHints : List (Option Nat) := [Block00.squareHints,Block01.squareHints,Block02.squareHints,Block03.squareHints,Block04.squareHints,Block05.squareHints,Block06.squareHints,Block07.squareHints,Block08.squareHints,Block09.squareHints,Block10.squareHints,Block11.squareHints,Block12.squareHints,Block13.squareHints,Block14.squareHints,Block15.squareHints,Block16.squareHints,Block17.squareHints,Block18.squareHints,Block19.squareHints,Block20.squareHints,Block21.squareHints,Block22.squareHints].flatten

set_option maxRecDepth 8192 in
private theorem square_checked : CF.check c1Rows c1Rows wideChunks c2Rows squareHints = true := by
  exact (CF.check_append _ _ _ _ _ _ _ _ Block00.square_checked (CF.check_append _ _ _ _ _ _ _ _ Block01.square_checked (CF.check_append _ _ _ _ _ _ _ _ Block02.square_checked (CF.check_append _ _ _ _ _ _ _ _ Block03.square_checked (CF.check_append _ _ _ _ _ _ _ _ Block04.square_checked (CF.check_append _ _ _ _ _ _ _ _ Block05.square_checked (CF.check_append _ _ _ _ _ _ _ _ Block06.square_checked (CF.check_append _ _ _ _ _ _ _ _ Block07.square_checked (CF.check_append _ _ _ _ _ _ _ _ Block08.square_checked (CF.check_append _ _ _ _ _ _ _ _ Block09.square_checked (CF.check_append _ _ _ _ _ _ _ _ Block10.square_checked (CF.check_append _ _ _ _ _ _ _ _ Block11.square_checked (CF.check_append _ _ _ _ _ _ _ _ Block12.square_checked (CF.check_append _ _ _ _ _ _ _ _ Block13.square_checked (CF.check_append _ _ _ _ _ _ _ _ Block14.square_checked (CF.check_append _ _ _ _ _ _ _ _ Block15.square_checked (CF.check_append _ _ _ _ _ _ _ _ Block16.square_checked (CF.check_append _ _ _ _ _ _ _ _ Block17.square_checked (CF.check_append _ _ _ _ _ _ _ _ Block18.square_checked (CF.check_append _ _ _ _ _ _ _ _ Block19.square_checked (CF.check_append _ _ _ _ _ _ _ _ Block20.square_checked (CF.check_append _ _ _ _ _ _ _ _ Block21.square_checked (CF.check_append _ _ _ _ _ _ _ _ Block22.square_checked (show CF.check [] c1Rows wideChunks [] [] = true from rfl))))))))))))))))))))))))

private def cubeHints : List (Option Nat) := [Block00.cubeHints,Block01.cubeHints,Block02.cubeHints,Block03.cubeHints,Block04.cubeHints,Block05.cubeHints,Block06.cubeHints,Block07.cubeHints,Block08.cubeHints,Block09.cubeHints,Block10.cubeHints,Block11.cubeHints,Block12.cubeHints,Block13.cubeHints,Block14.cubeHints,Block15.cubeHints,Block16.cubeHints,Block17.cubeHints,Block18.cubeHints,Block19.cubeHints,Block20.cubeHints,Block21.cubeHints,Block22.cubeHints].flatten

set_option maxRecDepth 8192 in
private theorem cube_checked : CF.check c2Rows c1Rows wideChunks c3Rows cubeHints = true := by
  exact (CF.check_append _ _ _ _ _ _ _ _ Block00.cube_checked (CF.check_append _ _ _ _ _ _ _ _ Block01.cube_checked (CF.check_append _ _ _ _ _ _ _ _ Block02.cube_checked (CF.check_append _ _ _ _ _ _ _ _ Block03.cube_checked (CF.check_append _ _ _ _ _ _ _ _ Block04.cube_checked (CF.check_append _ _ _ _ _ _ _ _ Block05.cube_checked (CF.check_append _ _ _ _ _ _ _ _ Block06.cube_checked (CF.check_append _ _ _ _ _ _ _ _ Block07.cube_checked (CF.check_append _ _ _ _ _ _ _ _ Block08.cube_checked (CF.check_append _ _ _ _ _ _ _ _ Block09.cube_checked (CF.check_append _ _ _ _ _ _ _ _ Block10.cube_checked (CF.check_append _ _ _ _ _ _ _ _ Block11.cube_checked (CF.check_append _ _ _ _ _ _ _ _ Block12.cube_checked (CF.check_append _ _ _ _ _ _ _ _ Block13.cube_checked (CF.check_append _ _ _ _ _ _ _ _ Block14.cube_checked (CF.check_append _ _ _ _ _ _ _ _ Block15.cube_checked (CF.check_append _ _ _ _ _ _ _ _ Block16.cube_checked (CF.check_append _ _ _ _ _ _ _ _ Block17.cube_checked (CF.check_append _ _ _ _ _ _ _ _ Block18.cube_checked (CF.check_append _ _ _ _ _ _ _ _ Block19.cube_checked (CF.check_append _ _ _ _ _ _ _ _ Block20.cube_checked (CF.check_append _ _ _ _ _ _ _ _ Block21.cube_checked (CF.check_append _ _ _ _ _ _ _ _ Block22.cube_checked (show CF.check [] c1Rows wideChunks [] [] = true from rfl))))))))))))))))))))))))
end LowPowers

set_option maxRecDepth 8192 in
/-- Checked literal product supplying h2 of the order-23 source-word assembly. -/
theorem low_square : Tables.c1 * Tables.c1 = Tables.c2 := by
  exact CF.product Tables.c1Rows Tables.c1Rows LowPowers.wideChunks Tables.c2Rows
    LowPowers.squareHints (by decide +kernel) (by decide +kernel)
    LowPowers.wide_correct LowPowers.square_checked

set_option maxRecDepth 8192 in
/-- Checked literal product supplying h3 of the order-23 source-word assembly. -/
theorem low_cube : Tables.c2 * Tables.c1 = Tables.c3 := by
  exact CF.product Tables.c2Rows Tables.c1Rows LowPowers.wideChunks Tables.c3Rows
    LowPowers.cubeHints (by decide +kernel) (by decide +kernel)
    LowPowers.wide_correct LowPowers.cube_checked

/-- Power two of the literal, untransposed ATLAS generator product. -/
theorem low_pow_two : (Data1242.first * Data1242.second) ^ 2 = Tables.c2 := by
  rw [pow_two, first_product]
  exact low_square

/-- Power three of the literal, untransposed ATLAS generator product. -/
theorem low_pow_three : (Data1242.first * Data1242.second) ^ 3 = Tables.c3 := by
  rw [pow_succ, low_pow_two, first_product]
  exact low_cube

end Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1242.ProductOrder23
