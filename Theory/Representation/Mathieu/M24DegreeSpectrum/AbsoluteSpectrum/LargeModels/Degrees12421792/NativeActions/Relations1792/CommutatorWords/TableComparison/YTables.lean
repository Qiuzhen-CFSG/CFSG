module

public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1792.CommutatorWords.TableComparison.YData

/-!
# Checked y tables

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
theorem yRows_length : yRows.flatten.length = 1792 := by decide +kernel

theorem yRows_width : ∀ r ∈ yRows, r.length = 32 := by
  have h : yRows.all (fun r => r.length == 32) = true := by decide +kernel
  intro r hr
  simpa only [beq_iff_eq] using List.all_eq_true.mp h r hr

set_option maxRecDepth 8192 in
theorem yTagged_eq : yTagged.flatten.map Prod.fst = yRows.flatten := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem yTagged_length : yTagged.flatten.length = 1792 := by decide +kernel


end Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1792.CommutatorWords.TableComparison
