module

public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1242.ProductOrder23.ClosingProducts.Thirteenth.Block00
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1242.ProductOrder23.ClosingProducts.Thirteenth.Block01
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1242.ProductOrder23.ClosingProducts.Thirteenth.Block02
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1242.ProductOrder23.ClosingProducts.Thirteenth.Block03
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1242.ProductOrder23.ClosingProducts.Thirteenth.Block04
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1242.ProductOrder23.ClosingProducts.Thirteenth.Block05
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1242.ProductOrder23.ClosingProducts.Thirteenth.Block06
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1242.ProductOrder23.ClosingProducts.Thirteenth.Block07
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1242.ProductOrder23.ClosingProducts.Thirteenth.Block08
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1242.ProductOrder23.ClosingProducts.Thirteenth.Block09
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1242.ProductOrder23.ClosingProducts.Thirteenth.Block10
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1242.ProductOrder23.ClosingProducts.Thirteenth.Block11
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1242.ProductOrder23.ClosingProducts.Thirteenth.Block12
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1242.ProductOrder23.ClosingProducts.Thirteenth.Block13
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1242.ProductOrder23.ClosingProducts.Thirteenth.Block14
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1242.ProductOrder23.ClosingProducts.Thirteenth.Block15
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1242.ProductOrder23.ClosingProducts.Thirteenth.Block16
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1242.ProductOrder23.ClosingProducts.Thirteenth.Block17
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1242.ProductOrder23.ClosingProducts.Thirteenth.Block18
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1242.ProductOrder23.ClosingProducts.Thirteenth.Block19
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1242.ProductOrder23.ClosingProducts.Thirteenth.Block20
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1242.ProductOrder23.ClosingProducts.Thirteenth.Block21
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1242.ProductOrder23.ClosingProducts.Thirteenth.Block22

/-! Complete checked assembly for the c10·c3 closing product. -/

public section
namespace Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1242.ProductOrder23.ClosingProducts.Thirteenth
open Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1242.ProductOrder23
open Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1242.ProductOrder23.Tables
open Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1242.ProductOrder23.ClosingProducts
open Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1792.Arithmetic

private def hints : List (Option Nat) := [Block00.hints,Block01.hints,Block02.hints,Block03.hints,Block04.hints,Block05.hints,Block06.hints,Block07.hints,Block08.hints,Block09.hints,Block10.hints,Block11.hints,Block12.hints,Block13.hints,Block14.hints,Block15.hints,Block16.hints,Block17.hints,Block18.hints,Block19.hints,Block20.hints,Block21.hints,Block22.hints].flatten

private theorem wide_correct : c3WideChunks.flatten = Tables.c3Rows.map (expandBlocks 18 69) := by
  simp only [c3WideChunks, Tables.c3Rows, Tables.c3Chunks,
    List.flatten_cons, List.flatten_nil, List.map_append, List.map_nil,
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

set_option maxRecDepth 8192 in
private theorem checked : CF.check Tables.c10Rows Tables.c3Rows c3WideChunks Tables.c13Rows hints = true := by
  exact (CF.check_append _ _ _ _ _ _ _ _ Block00.checked (CF.check_append _ _ _ _ _ _ _ _ Block01.checked (CF.check_append _ _ _ _ _ _ _ _ Block02.checked (CF.check_append _ _ _ _ _ _ _ _ Block03.checked (CF.check_append _ _ _ _ _ _ _ _ Block04.checked (CF.check_append _ _ _ _ _ _ _ _ Block05.checked (CF.check_append _ _ _ _ _ _ _ _ Block06.checked (CF.check_append _ _ _ _ _ _ _ _ Block07.checked (CF.check_append _ _ _ _ _ _ _ _ Block08.checked (CF.check_append _ _ _ _ _ _ _ _ Block09.checked (CF.check_append _ _ _ _ _ _ _ _ Block10.checked (CF.check_append _ _ _ _ _ _ _ _ Block11.checked (CF.check_append _ _ _ _ _ _ _ _ Block12.checked (CF.check_append _ _ _ _ _ _ _ _ Block13.checked (CF.check_append _ _ _ _ _ _ _ _ Block14.checked (CF.check_append _ _ _ _ _ _ _ _ Block15.checked (CF.check_append _ _ _ _ _ _ _ _ Block16.checked (CF.check_append _ _ _ _ _ _ _ _ Block17.checked (CF.check_append _ _ _ _ _ _ _ _ Block18.checked (CF.check_append _ _ _ _ _ _ _ _ Block19.checked (CF.check_append _ _ _ _ _ _ _ _ Block20.checked (CF.check_append _ _ _ _ _ _ _ _ Block21.checked (CF.check_append _ _ _ _ _ _ _ _ Block22.checked (show CF.check [] Tables.c3Rows c3WideChunks [] [] = true from rfl))))))))))))))))))))))))

set_option maxRecDepth 8192 in
theorem product : Tables.c10 * Tables.c3 = Tables.c13 := by
  have hp := CF.product Tables.c10Rows Tables.c3Rows c3WideChunks Tables.c13Rows hints
    (by decide +kernel) (by decide +kernel) wide_correct checked
  simpa only [Tables.c10, Tables.c3, Tables.c13] using hp

end Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1242.ProductOrder23.ClosingProducts.Thirteenth
