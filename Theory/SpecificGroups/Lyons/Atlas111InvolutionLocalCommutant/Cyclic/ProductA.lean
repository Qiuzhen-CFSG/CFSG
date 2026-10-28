module

public import Theory.SpecificGroups.Lyons.Atlas111InvolutionLocalCommutant.Cyclic.Data

/-!
# Checked product ab times q

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
private theorem aq_row0 :
    digitsEq 111 (rowProduct (abRows 0) qRows 111) (aqRows 0) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem aq_row1 :
    digitsEq 111 (rowProduct (abRows 1) qRows 111) (aqRows 1) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem aq_row2 :
    digitsEq 111 (rowProduct (abRows 2) qRows 111) (aqRows 2) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem aq_row3 :
    digitsEq 111 (rowProduct (abRows 3) qRows 111) (aqRows 3) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem aq_row4 :
    digitsEq 111 (rowProduct (abRows 4) qRows 111) (aqRows 4) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem aq_row5 :
    digitsEq 111 (rowProduct (abRows 5) qRows 111) (aqRows 5) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem aq_row6 :
    digitsEq 111 (rowProduct (abRows 6) qRows 111) (aqRows 6) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem aq_row7 :
    digitsEq 111 (rowProduct (abRows 7) qRows 111) (aqRows 7) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem aq_row8 :
    digitsEq 111 (rowProduct (abRows 8) qRows 111) (aqRows 8) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem aq_row9 :
    digitsEq 111 (rowProduct (abRows 9) qRows 111) (aqRows 9) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem aq_row10 :
    digitsEq 111 (rowProduct (abRows 10) qRows 111) (aqRows 10) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem aq_row11 :
    digitsEq 111 (rowProduct (abRows 11) qRows 111) (aqRows 11) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem aq_row12 :
    digitsEq 111 (rowProduct (abRows 12) qRows 111) (aqRows 12) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem aq_row13 :
    digitsEq 111 (rowProduct (abRows 13) qRows 111) (aqRows 13) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem aq_row14 :
    digitsEq 111 (rowProduct (abRows 14) qRows 111) (aqRows 14) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem aq_row15 :
    digitsEq 111 (rowProduct (abRows 15) qRows 111) (aqRows 15) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem aq_row16 :
    digitsEq 111 (rowProduct (abRows 16) qRows 111) (aqRows 16) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem aq_row17 :
    digitsEq 111 (rowProduct (abRows 17) qRows 111) (aqRows 17) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem aq_row18 :
    digitsEq 111 (rowProduct (abRows 18) qRows 111) (aqRows 18) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem aq_row19 :
    digitsEq 111 (rowProduct (abRows 19) qRows 111) (aqRows 19) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem aq_row20 :
    digitsEq 111 (rowProduct (abRows 20) qRows 111) (aqRows 20) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem aq_row21 :
    digitsEq 111 (rowProduct (abRows 21) qRows 111) (aqRows 21) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem aq_row22 :
    digitsEq 111 (rowProduct (abRows 22) qRows 111) (aqRows 22) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem aq_row23 :
    digitsEq 111 (rowProduct (abRows 23) qRows 111) (aqRows 23) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem aq_row24 :
    digitsEq 111 (rowProduct (abRows 24) qRows 111) (aqRows 24) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem aq_row25 :
    digitsEq 111 (rowProduct (abRows 25) qRows 111) (aqRows 25) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem aq_row26 :
    digitsEq 111 (rowProduct (abRows 26) qRows 111) (aqRows 26) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem aq_row27 :
    digitsEq 111 (rowProduct (abRows 27) qRows 111) (aqRows 27) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem aq_row28 :
    digitsEq 111 (rowProduct (abRows 28) qRows 111) (aqRows 28) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem aq_row29 :
    digitsEq 111 (rowProduct (abRows 29) qRows 111) (aqRows 29) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem aq_row30 :
    digitsEq 111 (rowProduct (abRows 30) qRows 111) (aqRows 30) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem aq_row31 :
    digitsEq 111 (rowProduct (abRows 31) qRows 111) (aqRows 31) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem aq_row32 :
    digitsEq 111 (rowProduct (abRows 32) qRows 111) (aqRows 32) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem aq_row33 :
    digitsEq 111 (rowProduct (abRows 33) qRows 111) (aqRows 33) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem aq_row34 :
    digitsEq 111 (rowProduct (abRows 34) qRows 111) (aqRows 34) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem aq_row35 :
    digitsEq 111 (rowProduct (abRows 35) qRows 111) (aqRows 35) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem aq_row36 :
    digitsEq 111 (rowProduct (abRows 36) qRows 111) (aqRows 36) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem aq_row37 :
    digitsEq 111 (rowProduct (abRows 37) qRows 111) (aqRows 37) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem aq_row38 :
    digitsEq 111 (rowProduct (abRows 38) qRows 111) (aqRows 38) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem aq_row39 :
    digitsEq 111 (rowProduct (abRows 39) qRows 111) (aqRows 39) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem aq_row40 :
    digitsEq 111 (rowProduct (abRows 40) qRows 111) (aqRows 40) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem aq_row41 :
    digitsEq 111 (rowProduct (abRows 41) qRows 111) (aqRows 41) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem aq_row42 :
    digitsEq 111 (rowProduct (abRows 42) qRows 111) (aqRows 42) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem aq_row43 :
    digitsEq 111 (rowProduct (abRows 43) qRows 111) (aqRows 43) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem aq_row44 :
    digitsEq 111 (rowProduct (abRows 44) qRows 111) (aqRows 44) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem aq_row45 :
    digitsEq 111 (rowProduct (abRows 45) qRows 111) (aqRows 45) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem aq_row46 :
    digitsEq 111 (rowProduct (abRows 46) qRows 111) (aqRows 46) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem aq_row47 :
    digitsEq 111 (rowProduct (abRows 47) qRows 111) (aqRows 47) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem aq_row48 :
    digitsEq 111 (rowProduct (abRows 48) qRows 111) (aqRows 48) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem aq_row49 :
    digitsEq 111 (rowProduct (abRows 49) qRows 111) (aqRows 49) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem aq_row50 :
    digitsEq 111 (rowProduct (abRows 50) qRows 111) (aqRows 50) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem aq_row51 :
    digitsEq 111 (rowProduct (abRows 51) qRows 111) (aqRows 51) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem aq_row52 :
    digitsEq 111 (rowProduct (abRows 52) qRows 111) (aqRows 52) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem aq_row53 :
    digitsEq 111 (rowProduct (abRows 53) qRows 111) (aqRows 53) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem aq_row54 :
    digitsEq 111 (rowProduct (abRows 54) qRows 111) (aqRows 54) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem aq_row55 :
    digitsEq 111 (rowProduct (abRows 55) qRows 111) (aqRows 55) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem aq_row56 :
    digitsEq 111 (rowProduct (abRows 56) qRows 111) (aqRows 56) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem aq_row57 :
    digitsEq 111 (rowProduct (abRows 57) qRows 111) (aqRows 57) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem aq_row58 :
    digitsEq 111 (rowProduct (abRows 58) qRows 111) (aqRows 58) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem aq_row59 :
    digitsEq 111 (rowProduct (abRows 59) qRows 111) (aqRows 59) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem aq_row60 :
    digitsEq 111 (rowProduct (abRows 60) qRows 111) (aqRows 60) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem aq_row61 :
    digitsEq 111 (rowProduct (abRows 61) qRows 111) (aqRows 61) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem aq_row62 :
    digitsEq 111 (rowProduct (abRows 62) qRows 111) (aqRows 62) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem aq_row63 :
    digitsEq 111 (rowProduct (abRows 63) qRows 111) (aqRows 63) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem aq_row64 :
    digitsEq 111 (rowProduct (abRows 64) qRows 111) (aqRows 64) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem aq_row65 :
    digitsEq 111 (rowProduct (abRows 65) qRows 111) (aqRows 65) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem aq_row66 :
    digitsEq 111 (rowProduct (abRows 66) qRows 111) (aqRows 66) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem aq_row67 :
    digitsEq 111 (rowProduct (abRows 67) qRows 111) (aqRows 67) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem aq_row68 :
    digitsEq 111 (rowProduct (abRows 68) qRows 111) (aqRows 68) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem aq_row69 :
    digitsEq 111 (rowProduct (abRows 69) qRows 111) (aqRows 69) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem aq_row70 :
    digitsEq 111 (rowProduct (abRows 70) qRows 111) (aqRows 70) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem aq_row71 :
    digitsEq 111 (rowProduct (abRows 71) qRows 111) (aqRows 71) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem aq_row72 :
    digitsEq 111 (rowProduct (abRows 72) qRows 111) (aqRows 72) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem aq_row73 :
    digitsEq 111 (rowProduct (abRows 73) qRows 111) (aqRows 73) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem aq_row74 :
    digitsEq 111 (rowProduct (abRows 74) qRows 111) (aqRows 74) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem aq_row75 :
    digitsEq 111 (rowProduct (abRows 75) qRows 111) (aqRows 75) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem aq_row76 :
    digitsEq 111 (rowProduct (abRows 76) qRows 111) (aqRows 76) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem aq_row77 :
    digitsEq 111 (rowProduct (abRows 77) qRows 111) (aqRows 77) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem aq_row78 :
    digitsEq 111 (rowProduct (abRows 78) qRows 111) (aqRows 78) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem aq_row79 :
    digitsEq 111 (rowProduct (abRows 79) qRows 111) (aqRows 79) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem aq_row80 :
    digitsEq 111 (rowProduct (abRows 80) qRows 111) (aqRows 80) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem aq_row81 :
    digitsEq 111 (rowProduct (abRows 81) qRows 111) (aqRows 81) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem aq_row82 :
    digitsEq 111 (rowProduct (abRows 82) qRows 111) (aqRows 82) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem aq_row83 :
    digitsEq 111 (rowProduct (abRows 83) qRows 111) (aqRows 83) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem aq_row84 :
    digitsEq 111 (rowProduct (abRows 84) qRows 111) (aqRows 84) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem aq_row85 :
    digitsEq 111 (rowProduct (abRows 85) qRows 111) (aqRows 85) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem aq_row86 :
    digitsEq 111 (rowProduct (abRows 86) qRows 111) (aqRows 86) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem aq_row87 :
    digitsEq 111 (rowProduct (abRows 87) qRows 111) (aqRows 87) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem aq_row88 :
    digitsEq 111 (rowProduct (abRows 88) qRows 111) (aqRows 88) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem aq_row89 :
    digitsEq 111 (rowProduct (abRows 89) qRows 111) (aqRows 89) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem aq_row90 :
    digitsEq 111 (rowProduct (abRows 90) qRows 111) (aqRows 90) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem aq_row91 :
    digitsEq 111 (rowProduct (abRows 91) qRows 111) (aqRows 91) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem aq_row92 :
    digitsEq 111 (rowProduct (abRows 92) qRows 111) (aqRows 92) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem aq_row93 :
    digitsEq 111 (rowProduct (abRows 93) qRows 111) (aqRows 93) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem aq_row94 :
    digitsEq 111 (rowProduct (abRows 94) qRows 111) (aqRows 94) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem aq_row95 :
    digitsEq 111 (rowProduct (abRows 95) qRows 111) (aqRows 95) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem aq_row96 :
    digitsEq 111 (rowProduct (abRows 96) qRows 111) (aqRows 96) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem aq_row97 :
    digitsEq 111 (rowProduct (abRows 97) qRows 111) (aqRows 97) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem aq_row98 :
    digitsEq 111 (rowProduct (abRows 98) qRows 111) (aqRows 98) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem aq_row99 :
    digitsEq 111 (rowProduct (abRows 99) qRows 111) (aqRows 99) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem aq_row100 :
    digitsEq 111 (rowProduct (abRows 100) qRows 111) (aqRows 100) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem aq_row101 :
    digitsEq 111 (rowProduct (abRows 101) qRows 111) (aqRows 101) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem aq_row102 :
    digitsEq 111 (rowProduct (abRows 102) qRows 111) (aqRows 102) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem aq_row103 :
    digitsEq 111 (rowProduct (abRows 103) qRows 111) (aqRows 103) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem aq_row104 :
    digitsEq 111 (rowProduct (abRows 104) qRows 111) (aqRows 104) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem aq_row105 :
    digitsEq 111 (rowProduct (abRows 105) qRows 111) (aqRows 105) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem aq_row106 :
    digitsEq 111 (rowProduct (abRows 106) qRows 111) (aqRows 106) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem aq_row107 :
    digitsEq 111 (rowProduct (abRows 107) qRows 111) (aqRows 107) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem aq_row108 :
    digitsEq 111 (rowProduct (abRows 108) qRows 111) (aqRows 108) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem aq_row109 :
    digitsEq 111 (rowProduct (abRows 109) qRows 111) (aqRows 109) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem aq_row110 :
    digitsEq 111 (rowProduct (abRows 110) qRows 111) (aqRows 110) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem aq_rows : ∀ i,
    digitsEq 111 (rowProduct (abRows i) qRows 111) (aqRows i) = true :=
  (Fin.cases aq_row0
    (Fin.cases aq_row1
    (Fin.cases aq_row2
    (Fin.cases aq_row3
    (Fin.cases aq_row4
    (Fin.cases aq_row5
    (Fin.cases aq_row6
    (Fin.cases aq_row7
    (Fin.cases aq_row8
    (Fin.cases aq_row9
    (Fin.cases aq_row10
    (Fin.cases aq_row11
    (Fin.cases aq_row12
    (Fin.cases aq_row13
    (Fin.cases aq_row14
    (Fin.cases aq_row15
    (Fin.cases aq_row16
    (Fin.cases aq_row17
    (Fin.cases aq_row18
    (Fin.cases aq_row19
    (Fin.cases aq_row20
    (Fin.cases aq_row21
    (Fin.cases aq_row22
    (Fin.cases aq_row23
    (Fin.cases aq_row24
    (Fin.cases aq_row25
    (Fin.cases aq_row26
    (Fin.cases aq_row27
    (Fin.cases aq_row28
    (Fin.cases aq_row29
    (Fin.cases aq_row30
    (Fin.cases aq_row31
    (Fin.cases aq_row32
    (Fin.cases aq_row33
    (Fin.cases aq_row34
    (Fin.cases aq_row35
    (Fin.cases aq_row36
    (Fin.cases aq_row37
    (Fin.cases aq_row38
    (Fin.cases aq_row39
    (Fin.cases aq_row40
    (Fin.cases aq_row41
    (Fin.cases aq_row42
    (Fin.cases aq_row43
    (Fin.cases aq_row44
    (Fin.cases aq_row45
    (Fin.cases aq_row46
    (Fin.cases aq_row47
    (Fin.cases aq_row48
    (Fin.cases aq_row49
    (Fin.cases aq_row50
    (Fin.cases aq_row51
    (Fin.cases aq_row52
    (Fin.cases aq_row53
    (Fin.cases aq_row54
    (Fin.cases aq_row55
    (Fin.cases aq_row56
    (Fin.cases aq_row57
    (Fin.cases aq_row58
    (Fin.cases aq_row59
    (Fin.cases aq_row60
    (Fin.cases aq_row61
    (Fin.cases aq_row62
    (Fin.cases aq_row63
    (Fin.cases aq_row64
    (Fin.cases aq_row65
    (Fin.cases aq_row66
    (Fin.cases aq_row67
    (Fin.cases aq_row68
    (Fin.cases aq_row69
    (Fin.cases aq_row70
    (Fin.cases aq_row71
    (Fin.cases aq_row72
    (Fin.cases aq_row73
    (Fin.cases aq_row74
    (Fin.cases aq_row75
    (Fin.cases aq_row76
    (Fin.cases aq_row77
    (Fin.cases aq_row78
    (Fin.cases aq_row79
    (Fin.cases aq_row80
    (Fin.cases aq_row81
    (Fin.cases aq_row82
    (Fin.cases aq_row83
    (Fin.cases aq_row84
    (Fin.cases aq_row85
    (Fin.cases aq_row86
    (Fin.cases aq_row87
    (Fin.cases aq_row88
    (Fin.cases aq_row89
    (Fin.cases aq_row90
    (Fin.cases aq_row91
    (Fin.cases aq_row92
    (Fin.cases aq_row93
    (Fin.cases aq_row94
    (Fin.cases aq_row95
    (Fin.cases aq_row96
    (Fin.cases aq_row97
    (Fin.cases aq_row98
    (Fin.cases aq_row99
    (Fin.cases aq_row100
    (Fin.cases aq_row101
    (Fin.cases aq_row102
    (Fin.cases aq_row103
    (Fin.cases aq_row104
    (Fin.cases aq_row105
    (Fin.cases aq_row106
    (Fin.cases aq_row107
    (Fin.cases aq_row108
    (Fin.cases aq_row109
    (Fin.cases aq_row110
    (fun i => Fin.elim0 i))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

public theorem mul_aq : abMatrix * qMatrix = aqMatrix :=
  decode_mul _ _ _ ab_small q_small aq_rows

end Lyons.SimplicityCertificate.LocalCommutant.Cyclic
