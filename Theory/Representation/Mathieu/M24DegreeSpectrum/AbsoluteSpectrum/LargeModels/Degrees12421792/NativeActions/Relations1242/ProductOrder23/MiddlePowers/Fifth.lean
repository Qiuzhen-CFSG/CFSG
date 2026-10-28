module

public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1242.ProductOrder23.MiddlePowers.Fifth.Block00
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1242.ProductOrder23.MiddlePowers.Fifth.Block01
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1242.ProductOrder23.MiddlePowers.Fifth.Block02
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1242.ProductOrder23.MiddlePowers.Fifth.Block03
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1242.ProductOrder23.MiddlePowers.Fifth.Block04
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1242.ProductOrder23.MiddlePowers.Fifth.Block05
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1242.ProductOrder23.MiddlePowers.Fifth.Block06
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1242.ProductOrder23.MiddlePowers.Fifth.Block07
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1242.ProductOrder23.MiddlePowers.Fifth.Block08
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1242.ProductOrder23.MiddlePowers.Fifth.Block09
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1242.ProductOrder23.MiddlePowers.Fifth.Block10
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1242.ProductOrder23.MiddlePowers.Fifth.Block11
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1242.ProductOrder23.MiddlePowers.Fifth.Block12
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1242.ProductOrder23.MiddlePowers.Fifth.Block13
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1242.ProductOrder23.MiddlePowers.Fifth.Block14
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1242.ProductOrder23.MiddlePowers.Fifth.Block15
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1242.ProductOrder23.MiddlePowers.Fifth.Block16
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1242.ProductOrder23.MiddlePowers.Fifth.Block17
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1242.ProductOrder23.MiddlePowers.Fifth.Block18
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1242.ProductOrder23.MiddlePowers.Fifth.Block19
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1242.ProductOrder23.MiddlePowers.Fifth.Block20
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1242.ProductOrder23.MiddlePowers.Fifth.Block21
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1242.ProductOrder23.MiddlePowers.Fifth.Block22

/-!
# Certificate assembly for c2 * c3 = c5

All 1242 rows are certified in bounded blocks. The independently checked
base-2048 expansion of the right factor justifies the carry-free checker.
The matrix product has the original untransposed ATLAS convention.
Source: M24G1-P1, word 2; see source/README.md.
-/

public section
namespace Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1242.ProductOrder23.MiddlePowers.Fifth
open Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1242.ProductOrder23
open Tables
open Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1792.Arithmetic

theorem wide_correct : Wide3.chunks.flatten = c3Rows.map (expandBlocks 18 69) := by
  simp only [Wide3.chunks, c3Rows, c3Chunks, List.flatten_cons, List.flatten_nil,
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
private theorem checked : CF.check c2Rows c3Rows Wide3.chunks c5Rows hints = true := by
  exact (CF.check_append _ _ _ _ _ _ _ _ Block00.checked
    (CF.check_append _ _ _ _ _ _ _ _ Block01.checked
    (CF.check_append _ _ _ _ _ _ _ _ Block02.checked
    (CF.check_append _ _ _ _ _ _ _ _ Block03.checked
    (CF.check_append _ _ _ _ _ _ _ _ Block04.checked
    (CF.check_append _ _ _ _ _ _ _ _ Block05.checked
    (CF.check_append _ _ _ _ _ _ _ _ Block06.checked
    (CF.check_append _ _ _ _ _ _ _ _ Block07.checked
    (CF.check_append _ _ _ _ _ _ _ _ Block08.checked
    (CF.check_append _ _ _ _ _ _ _ _ Block09.checked
    (CF.check_append _ _ _ _ _ _ _ _ Block10.checked
    (CF.check_append _ _ _ _ _ _ _ _ Block11.checked
    (CF.check_append _ _ _ _ _ _ _ _ Block12.checked
    (CF.check_append _ _ _ _ _ _ _ _ Block13.checked
    (CF.check_append _ _ _ _ _ _ _ _ Block14.checked
    (CF.check_append _ _ _ _ _ _ _ _ Block15.checked
    (CF.check_append _ _ _ _ _ _ _ _ Block16.checked
    (CF.check_append _ _ _ _ _ _ _ _ Block17.checked
    (CF.check_append _ _ _ _ _ _ _ _ Block18.checked
    (CF.check_append _ _ _ _ _ _ _ _ Block19.checked
    (CF.check_append _ _ _ _ _ _ _ _ Block20.checked
    (CF.check_append _ _ _ _ _ _ _ _ Block21.checked
    (CF.check_append _ _ _ _ _ _ _ _ Block22.checked
    (show CF.check [] c3Rows Wide3.chunks [] [] = true from rfl))))))))))))))))))))))))

set_option maxRecDepth 8192 in
/-- The complete checked literal matrix product. -/
theorem product : c2 * c3 = c5 := by
  exact CF.product c2Rows c3Rows Wide3.chunks c5Rows hints
    (by decide +kernel) (by decide +kernel) wide_correct checked

end Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1242.ProductOrder23.MiddlePowers.Fifth
