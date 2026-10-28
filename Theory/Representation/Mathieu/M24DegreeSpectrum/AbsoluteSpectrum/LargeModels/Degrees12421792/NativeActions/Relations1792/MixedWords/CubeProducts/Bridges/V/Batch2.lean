module

public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1792.MixedWords.CubeProducts.Bridges.V.Arithmetic

public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1792.MixedWords.CubeProducts.Inputs.V

/-!
# Checked widening of V, batch 2

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
theorem v_wide_16 :
    vWideBlock16 = Data.vBlock16.map (expandBlocks 32 56) := by
  apply VChecks.widening
  decide +kernel

set_option maxRecDepth 8192 in
theorem v_wide_17 :
    vWideBlock17 = Data.vBlock17.map (expandBlocks 32 56) := by
  apply VChecks.widening
  decide +kernel

set_option maxRecDepth 8192 in
theorem v_wide_18 :
    vWideBlock18 = Data.vBlock18.map (expandBlocks 32 56) := by
  apply VChecks.widening
  decide +kernel

set_option maxRecDepth 8192 in
theorem v_wide_19 :
    vWideBlock19 = Data.vBlock19.map (expandBlocks 32 56) := by
  apply VChecks.widening
  decide +kernel

set_option maxRecDepth 8192 in
theorem v_wide_20 :
    vWideBlock20 = Data.vBlock20.map (expandBlocks 32 56) := by
  apply VChecks.widening
  decide +kernel

set_option maxRecDepth 8192 in
theorem v_wide_21 :
    vWideBlock21 = Data.vBlock21.map (expandBlocks 32 56) := by
  apply VChecks.widening
  decide +kernel

set_option maxRecDepth 8192 in
theorem v_wide_22 :
    vWideBlock22 = Data.vBlock22.map (expandBlocks 32 56) := by
  apply VChecks.widening
  decide +kernel

set_option maxRecDepth 8192 in
theorem v_wide_23 :
    vWideBlock23 = Data.vBlock23.map (expandBlocks 32 56) := by
  apply VChecks.widening
  decide +kernel


end Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1792.MixedWords.CubeProducts
