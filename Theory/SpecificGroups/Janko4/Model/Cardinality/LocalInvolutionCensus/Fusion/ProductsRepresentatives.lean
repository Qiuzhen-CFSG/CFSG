module

public import Theory.SpecificGroups.Janko4.Model.Cardinality.LocalInvolutionCensus.Fusion.Tables

/-!
# Checked matrix products for census fusion: Common

Each packed GF(2) multiplication is proved by Lean kernel reduction.
The source words and attribution are documented in `Tables` and `source/README.md`.
-/

public section
namespace Janko4.Cardinality.LocalInvolutionCensus.FusionCertificates
open OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData
open LowerBound KernelSeparation
open Janko4.GeneratorCertificates
open Janko4.Cardinality.KernelCount
open Janko4.Cardinality.KernelCount.Relations (decoded_product eval_mul eval_inv)

set_option maxRecDepth 10000
set_option maxHeartbeats 800000

namespace Common

theorem product_20 : packedMul (factorRows 1) (factorRows 2) = kernel6At1Rows :=
  packedMul_eq_of_rows _ _ _ (by
    simp only [packedRow, factorRows, get_ofFn]
    decide +kernel)

theorem product_21 : packedMul (factorRows 3) (factorRows 4) = kernel26At3Rows :=
  packedMul_eq_of_rows _ _ _ (by
    simp only [packedRow, factorRows, get_ofFn]
    decide +kernel)

theorem product_22 : packedMul (factorRows 1) kernel26At3Rows = kernel26At1Rows :=
  packedMul_eq_of_rows _ _ _ (by
    simp only [packedRow, factorRows, get_ofFn]
    decide +kernel)

theorem product_23 : packedMul (factorRows 2) (factorRows 3) = kernel12At2Rows :=
  packedMul_eq_of_rows _ _ _ (by
    simp only [packedRow, factorRows, get_ofFn]
    decide +kernel)

theorem product_24 : packedMul (factorRows 5) (factorRows 8) = kernel304At5Rows :=
  packedMul_eq_of_rows _ _ _ (by
    simp only [packedRow, factorRows, get_ofFn]
    decide +kernel)

theorem product_25 : packedMul (factorRows 4) kernel304At5Rows = kernel304At4Rows :=
  packedMul_eq_of_rows _ _ _ (by
    simp only [packedRow, factorRows, get_ofFn]
    decide +kernel)

theorem product_26 : packedMul (factorRows 5) (factorRows 8) = kernel305At5Rows :=
  packedMul_eq_of_rows _ _ _ (by
    simp only [packedRow, factorRows, get_ofFn]
    decide +kernel)

theorem product_27 : packedMul (factorRows 4) kernel305At5Rows = kernel305At4Rows :=
  packedMul_eq_of_rows _ _ _ (by
    simp only [packedRow, factorRows, get_ofFn]
    decide +kernel)

theorem product_28 : packedMul (factorRows 0) kernel305At4Rows = kernel305At0Rows :=
  packedMul_eq_of_rows _ _ _ (by
    simp only [packedRow, factorRows, get_ofFn]
    decide +kernel)

theorem product_29 : packedMul (factorRows 0) (factorRows 0) = packedOne :=
  packedMul_eq_of_rows _ _ _ (by
    simp only [packedRow, factorRows, packedOne, get_ofFn]
    decide +kernel)

theorem product_30 : packedMul kernel6At1Rows (factorRows 0) = translate2Rows :=
  packedMul_eq_of_rows _ _ _ (by
    simp only [packedRow, factorRows, get_ofFn]
    decide +kernel)

theorem product_31 : packedMul kernel26At1Rows (factorRows 0) = translate3Rows :=
  packedMul_eq_of_rows _ _ _ (by
    simp only [packedRow, factorRows, get_ofFn]
    decide +kernel)

theorem product_32 : packedMul w10Rows (factorRows 0) = translate4Rows :=
  packedMul_eq_of_rows _ _ _ (by
    simp only [packedRow, factorRows, get_ofFn]
    decide +kernel)

theorem product_33 : packedMul lift2Rows (factorRows 0) = translate5Rows :=
  packedMul_eq_of_rows _ _ _ (by
    simp only [packedRow, factorRows, get_ofFn]
    decide +kernel)

theorem product_34 : packedMul (factorRows 0) lift2Rows = rep6Rows :=
  packedMul_eq_of_rows _ _ _ (by
    simp only [packedRow, factorRows, get_ofFn]
    decide +kernel)

theorem product_35 : packedMul rep6Rows (factorRows 0) = translate6Rows :=
  packedMul_eq_of_rows _ _ _ (by
    simp only [packedRow, factorRows, get_ofFn]
    decide +kernel)

theorem product_36 : packedMul lift3Rows (factorRows 0) = translate7Rows :=
  packedMul_eq_of_rows _ _ _ (by
    simp only [packedRow, factorRows, get_ofFn]
    decide +kernel)

theorem product_37 : packedMul kernel12At2Rows lift3Rows = rep8Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_38 : packedMul rep8Rows (factorRows 0) = translate8Rows :=
  packedMul_eq_of_rows _ _ _ (by
    simp only [packedRow, factorRows, get_ofFn]
    decide +kernel)

theorem product_39 : packedMul kernel304At4Rows lift3Rows = rep9Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_40 : packedMul rep9Rows (factorRows 0) = translate9Rows :=
  packedMul_eq_of_rows _ _ _ (by
    simp only [packedRow, factorRows, get_ofFn]
    decide +kernel)

theorem product_41 : packedMul kernel305At0Rows lift3Rows = rep10Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_42 : packedMul rep10Rows (factorRows 0) = translate10Rows :=
  packedMul_eq_of_rows _ _ _ (by
    simp only [packedRow, factorRows, get_ofFn]
    decide +kernel)

end Common
end Janko4.Cardinality.LocalInvolutionCensus.FusionCertificates
