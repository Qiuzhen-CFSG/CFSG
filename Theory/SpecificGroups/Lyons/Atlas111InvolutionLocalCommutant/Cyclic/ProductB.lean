module

public import Theory.SpecificGroups.Lyons.Atlas111InvolutionLocalCommutant.Cyclic.Data

/-!
# Checked product localB times q

The carry-free row arithmetic certifies this product over ZMod 5.

Source: the literal ATLAS local words and matrices; attribution in
`Atlas111Source/` and `Atlas111InvolutionSource/`. Reproduce these candidates
with `Cyclic/source/Generate.py`. All numerical checks use the Lean kernel.
-/

namespace Lyons.SimplicityCertificate.LocalCommutant.Cyclic

open Atlas111WordCertificate
open Words

set_option Elab.async false

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem bq_row0 :
    digitsEq 111 (rowProduct (localBRows 0) qRows 111) (bqRows 0) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem bq_row1 :
    digitsEq 111 (rowProduct (localBRows 1) qRows 111) (bqRows 1) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem bq_row2 :
    digitsEq 111 (rowProduct (localBRows 2) qRows 111) (bqRows 2) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem bq_row3 :
    digitsEq 111 (rowProduct (localBRows 3) qRows 111) (bqRows 3) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem bq_row4 :
    digitsEq 111 (rowProduct (localBRows 4) qRows 111) (bqRows 4) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem bq_row5 :
    digitsEq 111 (rowProduct (localBRows 5) qRows 111) (bqRows 5) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem bq_row6 :
    digitsEq 111 (rowProduct (localBRows 6) qRows 111) (bqRows 6) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem bq_row7 :
    digitsEq 111 (rowProduct (localBRows 7) qRows 111) (bqRows 7) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem bq_row8 :
    digitsEq 111 (rowProduct (localBRows 8) qRows 111) (bqRows 8) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem bq_row9 :
    digitsEq 111 (rowProduct (localBRows 9) qRows 111) (bqRows 9) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem bq_row10 :
    digitsEq 111 (rowProduct (localBRows 10) qRows 111) (bqRows 10) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem bq_row11 :
    digitsEq 111 (rowProduct (localBRows 11) qRows 111) (bqRows 11) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem bq_row12 :
    digitsEq 111 (rowProduct (localBRows 12) qRows 111) (bqRows 12) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem bq_row13 :
    digitsEq 111 (rowProduct (localBRows 13) qRows 111) (bqRows 13) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem bq_row14 :
    digitsEq 111 (rowProduct (localBRows 14) qRows 111) (bqRows 14) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem bq_row15 :
    digitsEq 111 (rowProduct (localBRows 15) qRows 111) (bqRows 15) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem bq_row16 :
    digitsEq 111 (rowProduct (localBRows 16) qRows 111) (bqRows 16) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem bq_row17 :
    digitsEq 111 (rowProduct (localBRows 17) qRows 111) (bqRows 17) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem bq_row18 :
    digitsEq 111 (rowProduct (localBRows 18) qRows 111) (bqRows 18) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem bq_row19 :
    digitsEq 111 (rowProduct (localBRows 19) qRows 111) (bqRows 19) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem bq_row20 :
    digitsEq 111 (rowProduct (localBRows 20) qRows 111) (bqRows 20) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem bq_row21 :
    digitsEq 111 (rowProduct (localBRows 21) qRows 111) (bqRows 21) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem bq_row22 :
    digitsEq 111 (rowProduct (localBRows 22) qRows 111) (bqRows 22) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem bq_row23 :
    digitsEq 111 (rowProduct (localBRows 23) qRows 111) (bqRows 23) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem bq_row24 :
    digitsEq 111 (rowProduct (localBRows 24) qRows 111) (bqRows 24) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem bq_row25 :
    digitsEq 111 (rowProduct (localBRows 25) qRows 111) (bqRows 25) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem bq_row26 :
    digitsEq 111 (rowProduct (localBRows 26) qRows 111) (bqRows 26) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem bq_row27 :
    digitsEq 111 (rowProduct (localBRows 27) qRows 111) (bqRows 27) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem bq_row28 :
    digitsEq 111 (rowProduct (localBRows 28) qRows 111) (bqRows 28) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem bq_row29 :
    digitsEq 111 (rowProduct (localBRows 29) qRows 111) (bqRows 29) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem bq_row30 :
    digitsEq 111 (rowProduct (localBRows 30) qRows 111) (bqRows 30) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem bq_row31 :
    digitsEq 111 (rowProduct (localBRows 31) qRows 111) (bqRows 31) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem bq_row32 :
    digitsEq 111 (rowProduct (localBRows 32) qRows 111) (bqRows 32) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem bq_row33 :
    digitsEq 111 (rowProduct (localBRows 33) qRows 111) (bqRows 33) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem bq_row34 :
    digitsEq 111 (rowProduct (localBRows 34) qRows 111) (bqRows 34) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem bq_row35 :
    digitsEq 111 (rowProduct (localBRows 35) qRows 111) (bqRows 35) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem bq_row36 :
    digitsEq 111 (rowProduct (localBRows 36) qRows 111) (bqRows 36) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem bq_row37 :
    digitsEq 111 (rowProduct (localBRows 37) qRows 111) (bqRows 37) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem bq_row38 :
    digitsEq 111 (rowProduct (localBRows 38) qRows 111) (bqRows 38) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem bq_row39 :
    digitsEq 111 (rowProduct (localBRows 39) qRows 111) (bqRows 39) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem bq_row40 :
    digitsEq 111 (rowProduct (localBRows 40) qRows 111) (bqRows 40) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem bq_row41 :
    digitsEq 111 (rowProduct (localBRows 41) qRows 111) (bqRows 41) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem bq_row42 :
    digitsEq 111 (rowProduct (localBRows 42) qRows 111) (bqRows 42) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem bq_row43 :
    digitsEq 111 (rowProduct (localBRows 43) qRows 111) (bqRows 43) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem bq_row44 :
    digitsEq 111 (rowProduct (localBRows 44) qRows 111) (bqRows 44) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem bq_row45 :
    digitsEq 111 (rowProduct (localBRows 45) qRows 111) (bqRows 45) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem bq_row46 :
    digitsEq 111 (rowProduct (localBRows 46) qRows 111) (bqRows 46) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem bq_row47 :
    digitsEq 111 (rowProduct (localBRows 47) qRows 111) (bqRows 47) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem bq_row48 :
    digitsEq 111 (rowProduct (localBRows 48) qRows 111) (bqRows 48) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem bq_row49 :
    digitsEq 111 (rowProduct (localBRows 49) qRows 111) (bqRows 49) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem bq_row50 :
    digitsEq 111 (rowProduct (localBRows 50) qRows 111) (bqRows 50) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem bq_row51 :
    digitsEq 111 (rowProduct (localBRows 51) qRows 111) (bqRows 51) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem bq_row52 :
    digitsEq 111 (rowProduct (localBRows 52) qRows 111) (bqRows 52) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem bq_row53 :
    digitsEq 111 (rowProduct (localBRows 53) qRows 111) (bqRows 53) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem bq_row54 :
    digitsEq 111 (rowProduct (localBRows 54) qRows 111) (bqRows 54) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem bq_row55 :
    digitsEq 111 (rowProduct (localBRows 55) qRows 111) (bqRows 55) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem bq_row56 :
    digitsEq 111 (rowProduct (localBRows 56) qRows 111) (bqRows 56) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem bq_row57 :
    digitsEq 111 (rowProduct (localBRows 57) qRows 111) (bqRows 57) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem bq_row58 :
    digitsEq 111 (rowProduct (localBRows 58) qRows 111) (bqRows 58) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem bq_row59 :
    digitsEq 111 (rowProduct (localBRows 59) qRows 111) (bqRows 59) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem bq_row60 :
    digitsEq 111 (rowProduct (localBRows 60) qRows 111) (bqRows 60) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem bq_row61 :
    digitsEq 111 (rowProduct (localBRows 61) qRows 111) (bqRows 61) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem bq_row62 :
    digitsEq 111 (rowProduct (localBRows 62) qRows 111) (bqRows 62) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem bq_row63 :
    digitsEq 111 (rowProduct (localBRows 63) qRows 111) (bqRows 63) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem bq_row64 :
    digitsEq 111 (rowProduct (localBRows 64) qRows 111) (bqRows 64) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem bq_row65 :
    digitsEq 111 (rowProduct (localBRows 65) qRows 111) (bqRows 65) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem bq_row66 :
    digitsEq 111 (rowProduct (localBRows 66) qRows 111) (bqRows 66) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem bq_row67 :
    digitsEq 111 (rowProduct (localBRows 67) qRows 111) (bqRows 67) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem bq_row68 :
    digitsEq 111 (rowProduct (localBRows 68) qRows 111) (bqRows 68) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem bq_row69 :
    digitsEq 111 (rowProduct (localBRows 69) qRows 111) (bqRows 69) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem bq_row70 :
    digitsEq 111 (rowProduct (localBRows 70) qRows 111) (bqRows 70) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem bq_row71 :
    digitsEq 111 (rowProduct (localBRows 71) qRows 111) (bqRows 71) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem bq_row72 :
    digitsEq 111 (rowProduct (localBRows 72) qRows 111) (bqRows 72) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem bq_row73 :
    digitsEq 111 (rowProduct (localBRows 73) qRows 111) (bqRows 73) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem bq_row74 :
    digitsEq 111 (rowProduct (localBRows 74) qRows 111) (bqRows 74) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem bq_row75 :
    digitsEq 111 (rowProduct (localBRows 75) qRows 111) (bqRows 75) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem bq_row76 :
    digitsEq 111 (rowProduct (localBRows 76) qRows 111) (bqRows 76) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem bq_row77 :
    digitsEq 111 (rowProduct (localBRows 77) qRows 111) (bqRows 77) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem bq_row78 :
    digitsEq 111 (rowProduct (localBRows 78) qRows 111) (bqRows 78) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem bq_row79 :
    digitsEq 111 (rowProduct (localBRows 79) qRows 111) (bqRows 79) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem bq_row80 :
    digitsEq 111 (rowProduct (localBRows 80) qRows 111) (bqRows 80) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem bq_row81 :
    digitsEq 111 (rowProduct (localBRows 81) qRows 111) (bqRows 81) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem bq_row82 :
    digitsEq 111 (rowProduct (localBRows 82) qRows 111) (bqRows 82) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem bq_row83 :
    digitsEq 111 (rowProduct (localBRows 83) qRows 111) (bqRows 83) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem bq_row84 :
    digitsEq 111 (rowProduct (localBRows 84) qRows 111) (bqRows 84) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem bq_row85 :
    digitsEq 111 (rowProduct (localBRows 85) qRows 111) (bqRows 85) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem bq_row86 :
    digitsEq 111 (rowProduct (localBRows 86) qRows 111) (bqRows 86) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem bq_row87 :
    digitsEq 111 (rowProduct (localBRows 87) qRows 111) (bqRows 87) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem bq_row88 :
    digitsEq 111 (rowProduct (localBRows 88) qRows 111) (bqRows 88) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem bq_row89 :
    digitsEq 111 (rowProduct (localBRows 89) qRows 111) (bqRows 89) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem bq_row90 :
    digitsEq 111 (rowProduct (localBRows 90) qRows 111) (bqRows 90) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem bq_row91 :
    digitsEq 111 (rowProduct (localBRows 91) qRows 111) (bqRows 91) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem bq_row92 :
    digitsEq 111 (rowProduct (localBRows 92) qRows 111) (bqRows 92) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem bq_row93 :
    digitsEq 111 (rowProduct (localBRows 93) qRows 111) (bqRows 93) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem bq_row94 :
    digitsEq 111 (rowProduct (localBRows 94) qRows 111) (bqRows 94) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem bq_row95 :
    digitsEq 111 (rowProduct (localBRows 95) qRows 111) (bqRows 95) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem bq_row96 :
    digitsEq 111 (rowProduct (localBRows 96) qRows 111) (bqRows 96) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem bq_row97 :
    digitsEq 111 (rowProduct (localBRows 97) qRows 111) (bqRows 97) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem bq_row98 :
    digitsEq 111 (rowProduct (localBRows 98) qRows 111) (bqRows 98) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem bq_row99 :
    digitsEq 111 (rowProduct (localBRows 99) qRows 111) (bqRows 99) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem bq_row100 :
    digitsEq 111 (rowProduct (localBRows 100) qRows 111) (bqRows 100) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem bq_row101 :
    digitsEq 111 (rowProduct (localBRows 101) qRows 111) (bqRows 101) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem bq_row102 :
    digitsEq 111 (rowProduct (localBRows 102) qRows 111) (bqRows 102) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem bq_row103 :
    digitsEq 111 (rowProduct (localBRows 103) qRows 111) (bqRows 103) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem bq_row104 :
    digitsEq 111 (rowProduct (localBRows 104) qRows 111) (bqRows 104) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem bq_row105 :
    digitsEq 111 (rowProduct (localBRows 105) qRows 111) (bqRows 105) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem bq_row106 :
    digitsEq 111 (rowProduct (localBRows 106) qRows 111) (bqRows 106) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem bq_row107 :
    digitsEq 111 (rowProduct (localBRows 107) qRows 111) (bqRows 107) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem bq_row108 :
    digitsEq 111 (rowProduct (localBRows 108) qRows 111) (bqRows 108) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem bq_row109 :
    digitsEq 111 (rowProduct (localBRows 109) qRows 111) (bqRows 109) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem bq_row110 :
    digitsEq 111 (rowProduct (localBRows 110) qRows 111) (bqRows 110) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bq_rows : ∀ i,
    digitsEq 111 (rowProduct (localBRows i) qRows 111) (bqRows i) = true :=
  (Fin.cases bq_row0
    (Fin.cases bq_row1
    (Fin.cases bq_row2
    (Fin.cases bq_row3
    (Fin.cases bq_row4
    (Fin.cases bq_row5
    (Fin.cases bq_row6
    (Fin.cases bq_row7
    (Fin.cases bq_row8
    (Fin.cases bq_row9
    (Fin.cases bq_row10
    (Fin.cases bq_row11
    (Fin.cases bq_row12
    (Fin.cases bq_row13
    (Fin.cases bq_row14
    (Fin.cases bq_row15
    (Fin.cases bq_row16
    (Fin.cases bq_row17
    (Fin.cases bq_row18
    (Fin.cases bq_row19
    (Fin.cases bq_row20
    (Fin.cases bq_row21
    (Fin.cases bq_row22
    (Fin.cases bq_row23
    (Fin.cases bq_row24
    (Fin.cases bq_row25
    (Fin.cases bq_row26
    (Fin.cases bq_row27
    (Fin.cases bq_row28
    (Fin.cases bq_row29
    (Fin.cases bq_row30
    (Fin.cases bq_row31
    (Fin.cases bq_row32
    (Fin.cases bq_row33
    (Fin.cases bq_row34
    (Fin.cases bq_row35
    (Fin.cases bq_row36
    (Fin.cases bq_row37
    (Fin.cases bq_row38
    (Fin.cases bq_row39
    (Fin.cases bq_row40
    (Fin.cases bq_row41
    (Fin.cases bq_row42
    (Fin.cases bq_row43
    (Fin.cases bq_row44
    (Fin.cases bq_row45
    (Fin.cases bq_row46
    (Fin.cases bq_row47
    (Fin.cases bq_row48
    (Fin.cases bq_row49
    (Fin.cases bq_row50
    (Fin.cases bq_row51
    (Fin.cases bq_row52
    (Fin.cases bq_row53
    (Fin.cases bq_row54
    (Fin.cases bq_row55
    (Fin.cases bq_row56
    (Fin.cases bq_row57
    (Fin.cases bq_row58
    (Fin.cases bq_row59
    (Fin.cases bq_row60
    (Fin.cases bq_row61
    (Fin.cases bq_row62
    (Fin.cases bq_row63
    (Fin.cases bq_row64
    (Fin.cases bq_row65
    (Fin.cases bq_row66
    (Fin.cases bq_row67
    (Fin.cases bq_row68
    (Fin.cases bq_row69
    (Fin.cases bq_row70
    (Fin.cases bq_row71
    (Fin.cases bq_row72
    (Fin.cases bq_row73
    (Fin.cases bq_row74
    (Fin.cases bq_row75
    (Fin.cases bq_row76
    (Fin.cases bq_row77
    (Fin.cases bq_row78
    (Fin.cases bq_row79
    (Fin.cases bq_row80
    (Fin.cases bq_row81
    (Fin.cases bq_row82
    (Fin.cases bq_row83
    (Fin.cases bq_row84
    (Fin.cases bq_row85
    (Fin.cases bq_row86
    (Fin.cases bq_row87
    (Fin.cases bq_row88
    (Fin.cases bq_row89
    (Fin.cases bq_row90
    (Fin.cases bq_row91
    (Fin.cases bq_row92
    (Fin.cases bq_row93
    (Fin.cases bq_row94
    (Fin.cases bq_row95
    (Fin.cases bq_row96
    (Fin.cases bq_row97
    (Fin.cases bq_row98
    (Fin.cases bq_row99
    (Fin.cases bq_row100
    (Fin.cases bq_row101
    (Fin.cases bq_row102
    (Fin.cases bq_row103
    (Fin.cases bq_row104
    (Fin.cases bq_row105
    (Fin.cases bq_row106
    (Fin.cases bq_row107
    (Fin.cases bq_row108
    (Fin.cases bq_row109
    (Fin.cases bq_row110
    (fun i => Fin.elim0 i))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

public theorem mul_bq : localBMatrix * qMatrix = bqMatrix :=
  decode_mul _ _ _ localB_small q_small bq_rows

end Lyons.SimplicityCertificate.LocalCommutant.Cyclic
