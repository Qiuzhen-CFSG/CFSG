module

public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1792.MixedWords.CubeProducts.Bridges.V.Arithmetic

public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1792.MixedWords.CubeProducts.Inputs.V

/-!
# Checked widening of V, batch 0

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
theorem v_wide_0 :
    vWideBlock0 = Data.vBlock0.map (expandBlocks 32 56) := by
  apply VChecks.widening
  decide +kernel

set_option maxRecDepth 8192 in
theorem v_wide_1 :
    vWideBlock1 = Data.vBlock1.map (expandBlocks 32 56) := by
  apply VChecks.widening
  decide +kernel

set_option maxRecDepth 8192 in
theorem v_wide_2 :
    vWideBlock2 = Data.vBlock2.map (expandBlocks 32 56) := by
  apply VChecks.widening
  decide +kernel

set_option maxRecDepth 8192 in
theorem v_wide_3 :
    vWideBlock3 = Data.vBlock3.map (expandBlocks 32 56) := by
  apply VChecks.widening
  decide +kernel

set_option maxRecDepth 8192 in
theorem v_wide_4 :
    vWideBlock4 = Data.vBlock4.map (expandBlocks 32 56) := by
  apply VChecks.widening
  decide +kernel

set_option maxRecDepth 8192 in
theorem v_wide_5 :
    vWideBlock5 = Data.vBlock5.map (expandBlocks 32 56) := by
  apply VChecks.widening
  decide +kernel

set_option maxRecDepth 8192 in
theorem v_wide_6 :
    vWideBlock6 = Data.vBlock6.map (expandBlocks 32 56) := by
  apply VChecks.widening
  decide +kernel

set_option maxRecDepth 8192 in
theorem v_wide_7 :
    vWideBlock7 = Data.vBlock7.map (expandBlocks 32 56) := by
  apply VChecks.widening
  decide +kernel


end Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1792.MixedWords.CubeProducts
