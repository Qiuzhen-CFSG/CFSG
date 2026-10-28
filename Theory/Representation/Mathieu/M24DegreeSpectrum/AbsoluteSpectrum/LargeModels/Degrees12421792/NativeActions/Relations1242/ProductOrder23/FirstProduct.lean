module

public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1242.ProductOrder23.FirstProduct.Block00
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1242.ProductOrder23.FirstProduct.Block01
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1242.ProductOrder23.FirstProduct.Block02
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1242.ProductOrder23.FirstProduct.Block03
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1242.ProductOrder23.FirstProduct.Block04
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1242.ProductOrder23.FirstProduct.Block05
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1242.ProductOrder23.FirstProduct.Block06
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1242.ProductOrder23.FirstProduct.Block07
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1242.ProductOrder23.FirstProduct.Block08
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1242.ProductOrder23.FirstProduct.Block09
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1242.ProductOrder23.FirstProduct.Block10
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1242.ProductOrder23.FirstProduct.Block11
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1242.ProductOrder23.FirstProduct.Block12
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1242.ProductOrder23.FirstProduct.Block13
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1242.ProductOrder23.FirstProduct.Block14
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1242.ProductOrder23.FirstProduct.Block15
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1242.ProductOrder23.FirstProduct.Block16
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1242.ProductOrder23.FirstProduct.Block17
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1242.ProductOrder23.FirstProduct.Block18
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1242.ProductOrder23.FirstProduct.Block19
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1242.ProductOrder23.FirstProduct.Block20
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1242.ProductOrder23.FirstProduct.Block21
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1242.ProductOrder23.FirstProduct.Block22

/-!
# The literal degree-1242 ATLAS generator product

The 23 bounded row blocks certify every row of the original untransposed
product. Independently checked expansion tables connect the dense carry-free
branch to the stored second generator; sparse hints are checked as well.
No generator-order or native-action premise occurs in this theorem.
Source: M24G1-f2r1242B0.m1/.m2 and M24G1-P1, word 2; see source/README.md.
-/

public section
namespace Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1242.ProductOrder23
open Thompson.BinaryMatrix
open Relations1792.Arithmetic
namespace FirstProduct
open Tables

theorem wide_correct : bWideChunks.flatten = bRows.map (expandBlocks 18 69) := by
  simp only [bWideChunks, bRows, bChunks, List.flatten_cons, List.flatten_nil,
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

private def hints : List (Option Nat) := [Block00.hints,Block01.hints,Block02.hints,Block03.hints,Block04.hints,Block05.hints,Block06.hints,Block07.hints,Block08.hints,Block09.hints,Block10.hints,Block11.hints,Block12.hints,Block13.hints,Block14.hints,Block15.hints,Block16.hints,Block17.hints,Block18.hints,Block19.hints,Block20.hints,Block21.hints,Block22.hints].flatten

set_option maxRecDepth 8192 in
private theorem checked : CF.check aRows bRows bWideChunks c1Rows hints = true := by
  exact (CF.check_append _ _ _ _ _ _ _ _ Block00.checked (CF.check_append _ _ _ _ _ _ _ _ Block01.checked (CF.check_append _ _ _ _ _ _ _ _ Block02.checked (CF.check_append _ _ _ _ _ _ _ _ Block03.checked (CF.check_append _ _ _ _ _ _ _ _ Block04.checked (CF.check_append _ _ _ _ _ _ _ _ Block05.checked (CF.check_append _ _ _ _ _ _ _ _ Block06.checked (CF.check_append _ _ _ _ _ _ _ _ Block07.checked (CF.check_append _ _ _ _ _ _ _ _ Block08.checked (CF.check_append _ _ _ _ _ _ _ _ Block09.checked (CF.check_append _ _ _ _ _ _ _ _ Block10.checked (CF.check_append _ _ _ _ _ _ _ _ Block11.checked (CF.check_append _ _ _ _ _ _ _ _ Block12.checked (CF.check_append _ _ _ _ _ _ _ _ Block13.checked (CF.check_append _ _ _ _ _ _ _ _ Block14.checked (CF.check_append _ _ _ _ _ _ _ _ Block15.checked (CF.check_append _ _ _ _ _ _ _ _ Block16.checked (CF.check_append _ _ _ _ _ _ _ _ Block17.checked (CF.check_append _ _ _ _ _ _ _ _ Block18.checked (CF.check_append _ _ _ _ _ _ _ _ Block19.checked (CF.check_append _ _ _ _ _ _ _ _ Block20.checked (CF.check_append _ _ _ _ _ _ _ _ Block21.checked (CF.check_append _ _ _ _ _ _ _ _ Block22.checked (show CF.check [] bRows bWideChunks [] [] = true from rfl))))))))))))))))))))))))

set_option maxRecDepth 8192 in
private theorem aRows_eq : aRows.toArray = Data1242.firstRows := by rfl

set_option maxRecDepth 8192 in
private theorem bRows_eq : bRows.toArray = Data1242.secondRows := by rfl
end FirstProduct

set_option maxRecDepth 8192 in
/-- All rows of the literal written product of the two ATLAS generators. -/
theorem first_product : Data1242.first * Data1242.second = Tables.c1 := by
  have hp := CF.product Tables.aRows Tables.bRows Tables.bWideChunks Tables.c1Rows
    FirstProduct.hints (by decide +kernel) (by decide +kernel)
    FirstProduct.wide_correct FirstProduct.checked
  simpa only [Data1242.first, Data1242.second, Tables.c1,
    FirstProduct.aRows_eq, FirstProduct.bRows_eq] using hp

end Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1242.ProductOrder23
