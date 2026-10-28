module

public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1792.ProductOrder23.HighProducts.Checker
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1792.ProductOrder23.HighProducts.NumericTables

/-!
# Complete comparisons with the published matrices

Every numeric table is compared with the complete original candidate list.
The closing comparison includes all 1792 rows of the actual identity.

Source: ATLAS M24G1-f2r1792B0, word 2 of M24G1-P1.
See `HighProducts/source/README.md` and `ProductOrder23/source/README.md`.
-/

@[expose] public section
namespace Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1792.ProductOrder23.HighProducts.Tables

set_option maxRecDepth 8192 in
theorem right3_eq : right3.flatten = Data.power3Rows := by decide +kernel

set_option maxRecDepth 8192 in
theorem right3_width : right3.all (fun b => b.length == 16) = true := by decide +kernel

theorem right3_length (b : List Nat) (hb : b ∈ right3) : b.length = 16 := by
  exact of_decide_eq_true (List.all_eq_true.mp right3_width b hb)

set_option maxRecDepth 8192 in
theorem right10_eq : right10.flatten = Data.power10Rows := by decide +kernel

set_option maxRecDepth 8192 in
theorem right10_width : right10.all (fun b => b.length == 16) = true := by decide +kernel

theorem right10_length (b : List Nat) (hb : b ∈ right10) : b.length = 16 := by
  exact of_decide_eq_true (List.all_eq_true.mp right10_width b hb)

set_option maxRecDepth 8192 in
theorem segments10_eq : segments10.flatten = Data.power10Rows := by decide +kernel

set_option maxRecDepth 8192 in
theorem segments20_eq : segments20.flatten = Data.power20Rows := by decide +kernel

set_option maxRecDepth 8192 in
theorem segments23_eq : segments23.flatten = identityRows 1792 := by decide +kernel

end Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1792.ProductOrder23.HighProducts.Tables
