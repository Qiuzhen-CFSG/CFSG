module

public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1792.MixedWords.CubeProducts.Bridges.V.Arithmetic

public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1792.MixedWords.CubeProducts.Inputs.V

/-!
# Checked widening of V, batch 6

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
theorem v_wide_48 :
    vWideBlock48 = Data.vBlock48.map (expandBlocks 32 56) := by
  apply VChecks.widening
  decide +kernel

set_option maxRecDepth 8192 in
theorem v_wide_49 :
    vWideBlock49 = Data.vBlock49.map (expandBlocks 32 56) := by
  apply VChecks.widening
  decide +kernel

set_option maxRecDepth 8192 in
theorem v_wide_50 :
    vWideBlock50 = Data.vBlock50.map (expandBlocks 32 56) := by
  apply VChecks.widening
  decide +kernel

set_option maxRecDepth 8192 in
theorem v_wide_51 :
    vWideBlock51 = Data.vBlock51.map (expandBlocks 32 56) := by
  apply VChecks.widening
  decide +kernel

set_option maxRecDepth 8192 in
theorem v_wide_52 :
    vWideBlock52 = Data.vBlock52.map (expandBlocks 32 56) := by
  apply VChecks.widening
  decide +kernel

set_option maxRecDepth 8192 in
theorem v_wide_53 :
    vWideBlock53 = Data.vBlock53.map (expandBlocks 32 56) := by
  apply VChecks.widening
  decide +kernel

set_option maxRecDepth 8192 in
theorem v_wide_54 :
    vWideBlock54 = Data.vBlock54.map (expandBlocks 32 56) := by
  apply VChecks.widening
  decide +kernel

set_option maxRecDepth 8192 in
theorem v_wide_55 :
    vWideBlock55 = Data.vBlock55.map (expandBlocks 32 56) := by
  apply VChecks.widening
  decide +kernel


end Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1792.MixedWords.CubeProducts
