module

public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1792.MixedWords.CubeProducts.Bridges.V.Arithmetic

public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1792.MixedWords.CubeProducts.Inputs.V

/-!
# Checked widening of V, batch 5

Adapted from `CubeProducts/source/generate.py` using proved bounded arithmetic. Every numerical equation is
checked by the Lean kernel. Source: ATLAS M24G1-P1; see the two
`source/README.md` files in MixedWords and CubeProducts.
-/

@[expose] public section
namespace Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1792.MixedWords.CubeProducts
open Arithmetic

open Inputs

set_option Elab.async false

set_option maxRecDepth 8192 in
theorem v_wide_40 :
    vWideBlock40 = Data.vBlock40.map (expandBlocks 32 56) := by
  apply VChecks.widening
  decide +kernel

set_option maxRecDepth 8192 in
theorem v_wide_41 :
    vWideBlock41 = Data.vBlock41.map (expandBlocks 32 56) := by
  apply VChecks.widening
  decide +kernel

set_option maxRecDepth 8192 in
theorem v_wide_42 :
    vWideBlock42 = Data.vBlock42.map (expandBlocks 32 56) := by
  apply VChecks.widening
  decide +kernel

set_option maxRecDepth 8192 in
theorem v_wide_43 :
    vWideBlock43 = Data.vBlock43.map (expandBlocks 32 56) := by
  apply VChecks.widening
  decide +kernel

set_option maxRecDepth 8192 in
theorem v_wide_44 :
    vWideBlock44 = Data.vBlock44.map (expandBlocks 32 56) := by
  apply VChecks.widening
  decide +kernel

set_option maxRecDepth 8192 in
theorem v_wide_45 :
    vWideBlock45 = Data.vBlock45.map (expandBlocks 32 56) := by
  apply VChecks.widening
  decide +kernel

set_option maxRecDepth 8192 in
theorem v_wide_46 :
    vWideBlock46 = Data.vBlock46.map (expandBlocks 32 56) := by
  apply VChecks.widening
  decide +kernel

set_option maxRecDepth 8192 in
theorem v_wide_47 :
    vWideBlock47 = Data.vBlock47.map (expandBlocks 32 56) := by
  apply VChecks.widening
  decide +kernel


end Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1792.MixedWords.CubeProducts
