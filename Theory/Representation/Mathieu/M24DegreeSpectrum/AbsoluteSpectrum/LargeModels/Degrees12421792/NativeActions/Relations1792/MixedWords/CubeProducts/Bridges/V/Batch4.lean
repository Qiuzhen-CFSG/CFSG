module

public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1792.MixedWords.CubeProducts.Bridges.V.Arithmetic

public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1792.MixedWords.CubeProducts.Inputs.V

/-!
# Checked widening of V, batch 4

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
theorem v_wide_32 :
    vWideBlock32 = Data.vBlock32.map (expandBlocks 32 56) := by
  apply VChecks.widening
  decide +kernel

set_option maxRecDepth 8192 in
theorem v_wide_33 :
    vWideBlock33 = Data.vBlock33.map (expandBlocks 32 56) := by
  apply VChecks.widening
  decide +kernel

set_option maxRecDepth 8192 in
theorem v_wide_34 :
    vWideBlock34 = Data.vBlock34.map (expandBlocks 32 56) := by
  apply VChecks.widening
  decide +kernel

set_option maxRecDepth 8192 in
theorem v_wide_35 :
    vWideBlock35 = Data.vBlock35.map (expandBlocks 32 56) := by
  apply VChecks.widening
  decide +kernel

set_option maxRecDepth 8192 in
theorem v_wide_36 :
    vWideBlock36 = Data.vBlock36.map (expandBlocks 32 56) := by
  apply VChecks.widening
  decide +kernel

set_option maxRecDepth 8192 in
theorem v_wide_37 :
    vWideBlock37 = Data.vBlock37.map (expandBlocks 32 56) := by
  apply VChecks.widening
  decide +kernel

set_option maxRecDepth 8192 in
theorem v_wide_38 :
    vWideBlock38 = Data.vBlock38.map (expandBlocks 32 56) := by
  apply VChecks.widening
  decide +kernel

set_option maxRecDepth 8192 in
theorem v_wide_39 :
    vWideBlock39 = Data.vBlock39.map (expandBlocks 32 56) := by
  apply VChecks.widening
  decide +kernel


end Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1792.MixedWords.CubeProducts
