module

public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1792.CommutatorWords.TableComparison.VData
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1792.CommutatorWords.Data

/-!
# Checked v tables

Every radix expansion, shape assertion and table bridge is kernel checked.
The matrices retain the original ATLAS row convention. Numeric generation is
untrusted; every used table comparison is checked in Lean. Source: ATLAS
M24G1-P1 and M24G1-f2r1792B0.m1/.m2; see `source/README.md`.
-/

public section
namespace Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1792.CommutatorWords.TableComparison
open Arithmetic GeneratorOrders

set_option Elab.async false

set_option maxRecDepth 8192 in
theorem vRows_length : vRows.flatten.length = 1792 := by decide +kernel

theorem vRows_width : ∀ r ∈ vRows, r.length = 32 := by
  have h : vRows.all (fun r => r.length == 32) = true := by decide +kernel
  intro r hr
  simpa only [beq_iff_eq] using List.all_eq_true.mp h r hr

set_option maxRecDepth 8192 in
theorem vRows_eq : vRows.flatten = Data.wordFourRows.toList := by decide +kernel

theorem vRows_decode : decodeRows 1792 vRows.flatten = Data.wordFour := by
  rw [vRows_eq, decodeRows_array]
  rfl


end Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1792.CommutatorWords.TableComparison
