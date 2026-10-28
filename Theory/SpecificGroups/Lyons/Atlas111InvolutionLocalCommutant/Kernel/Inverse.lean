module

public import Theory.SpecificGroups.Lyons.Atlas111InvolutionLocalCommutant.Kernel.Data

/-!
# Left inverse for the augmented annihilator

Carry-free row products certify D N = I. This identity makes the first
109 annihilator equations and coordinates 0 and 2 determine a vector uniquely.

Candidate generation and source attribution: `Kernel/source/GenerateKernel.py`
and `Kernel/source/README.md`. Every numerical assertion is checked in Lean.
-/

namespace Lyons.SimplicityCertificate.LocalCommutant.Kernel

open Atlas111WordCertificate

set_option Elab.async false

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem inverse_row0 :
    digitsEq 111 (rowProduct (dRows 0) nRows 111) (oneRows 0) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem inverse_row1 :
    digitsEq 111 (rowProduct (dRows 1) nRows 111) (oneRows 1) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem inverse_row2 :
    digitsEq 111 (rowProduct (dRows 2) nRows 111) (oneRows 2) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem inverse_row3 :
    digitsEq 111 (rowProduct (dRows 3) nRows 111) (oneRows 3) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem inverse_row4 :
    digitsEq 111 (rowProduct (dRows 4) nRows 111) (oneRows 4) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem inverse_row5 :
    digitsEq 111 (rowProduct (dRows 5) nRows 111) (oneRows 5) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem inverse_row6 :
    digitsEq 111 (rowProduct (dRows 6) nRows 111) (oneRows 6) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem inverse_row7 :
    digitsEq 111 (rowProduct (dRows 7) nRows 111) (oneRows 7) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem inverse_row8 :
    digitsEq 111 (rowProduct (dRows 8) nRows 111) (oneRows 8) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem inverse_row9 :
    digitsEq 111 (rowProduct (dRows 9) nRows 111) (oneRows 9) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem inverse_row10 :
    digitsEq 111 (rowProduct (dRows 10) nRows 111) (oneRows 10) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem inverse_row11 :
    digitsEq 111 (rowProduct (dRows 11) nRows 111) (oneRows 11) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem inverse_row12 :
    digitsEq 111 (rowProduct (dRows 12) nRows 111) (oneRows 12) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem inverse_row13 :
    digitsEq 111 (rowProduct (dRows 13) nRows 111) (oneRows 13) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem inverse_row14 :
    digitsEq 111 (rowProduct (dRows 14) nRows 111) (oneRows 14) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem inverse_row15 :
    digitsEq 111 (rowProduct (dRows 15) nRows 111) (oneRows 15) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem inverse_row16 :
    digitsEq 111 (rowProduct (dRows 16) nRows 111) (oneRows 16) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem inverse_row17 :
    digitsEq 111 (rowProduct (dRows 17) nRows 111) (oneRows 17) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem inverse_row18 :
    digitsEq 111 (rowProduct (dRows 18) nRows 111) (oneRows 18) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem inverse_row19 :
    digitsEq 111 (rowProduct (dRows 19) nRows 111) (oneRows 19) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem inverse_row20 :
    digitsEq 111 (rowProduct (dRows 20) nRows 111) (oneRows 20) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem inverse_row21 :
    digitsEq 111 (rowProduct (dRows 21) nRows 111) (oneRows 21) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem inverse_row22 :
    digitsEq 111 (rowProduct (dRows 22) nRows 111) (oneRows 22) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem inverse_row23 :
    digitsEq 111 (rowProduct (dRows 23) nRows 111) (oneRows 23) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem inverse_row24 :
    digitsEq 111 (rowProduct (dRows 24) nRows 111) (oneRows 24) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem inverse_row25 :
    digitsEq 111 (rowProduct (dRows 25) nRows 111) (oneRows 25) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem inverse_row26 :
    digitsEq 111 (rowProduct (dRows 26) nRows 111) (oneRows 26) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem inverse_row27 :
    digitsEq 111 (rowProduct (dRows 27) nRows 111) (oneRows 27) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem inverse_row28 :
    digitsEq 111 (rowProduct (dRows 28) nRows 111) (oneRows 28) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem inverse_row29 :
    digitsEq 111 (rowProduct (dRows 29) nRows 111) (oneRows 29) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem inverse_row30 :
    digitsEq 111 (rowProduct (dRows 30) nRows 111) (oneRows 30) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem inverse_row31 :
    digitsEq 111 (rowProduct (dRows 31) nRows 111) (oneRows 31) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem inverse_row32 :
    digitsEq 111 (rowProduct (dRows 32) nRows 111) (oneRows 32) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem inverse_row33 :
    digitsEq 111 (rowProduct (dRows 33) nRows 111) (oneRows 33) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem inverse_row34 :
    digitsEq 111 (rowProduct (dRows 34) nRows 111) (oneRows 34) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem inverse_row35 :
    digitsEq 111 (rowProduct (dRows 35) nRows 111) (oneRows 35) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem inverse_row36 :
    digitsEq 111 (rowProduct (dRows 36) nRows 111) (oneRows 36) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem inverse_row37 :
    digitsEq 111 (rowProduct (dRows 37) nRows 111) (oneRows 37) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem inverse_row38 :
    digitsEq 111 (rowProduct (dRows 38) nRows 111) (oneRows 38) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem inverse_row39 :
    digitsEq 111 (rowProduct (dRows 39) nRows 111) (oneRows 39) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem inverse_row40 :
    digitsEq 111 (rowProduct (dRows 40) nRows 111) (oneRows 40) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem inverse_row41 :
    digitsEq 111 (rowProduct (dRows 41) nRows 111) (oneRows 41) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem inverse_row42 :
    digitsEq 111 (rowProduct (dRows 42) nRows 111) (oneRows 42) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem inverse_row43 :
    digitsEq 111 (rowProduct (dRows 43) nRows 111) (oneRows 43) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem inverse_row44 :
    digitsEq 111 (rowProduct (dRows 44) nRows 111) (oneRows 44) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem inverse_row45 :
    digitsEq 111 (rowProduct (dRows 45) nRows 111) (oneRows 45) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem inverse_row46 :
    digitsEq 111 (rowProduct (dRows 46) nRows 111) (oneRows 46) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem inverse_row47 :
    digitsEq 111 (rowProduct (dRows 47) nRows 111) (oneRows 47) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem inverse_row48 :
    digitsEq 111 (rowProduct (dRows 48) nRows 111) (oneRows 48) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem inverse_row49 :
    digitsEq 111 (rowProduct (dRows 49) nRows 111) (oneRows 49) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem inverse_row50 :
    digitsEq 111 (rowProduct (dRows 50) nRows 111) (oneRows 50) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem inverse_row51 :
    digitsEq 111 (rowProduct (dRows 51) nRows 111) (oneRows 51) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem inverse_row52 :
    digitsEq 111 (rowProduct (dRows 52) nRows 111) (oneRows 52) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem inverse_row53 :
    digitsEq 111 (rowProduct (dRows 53) nRows 111) (oneRows 53) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem inverse_row54 :
    digitsEq 111 (rowProduct (dRows 54) nRows 111) (oneRows 54) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem inverse_row55 :
    digitsEq 111 (rowProduct (dRows 55) nRows 111) (oneRows 55) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem inverse_row56 :
    digitsEq 111 (rowProduct (dRows 56) nRows 111) (oneRows 56) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem inverse_row57 :
    digitsEq 111 (rowProduct (dRows 57) nRows 111) (oneRows 57) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem inverse_row58 :
    digitsEq 111 (rowProduct (dRows 58) nRows 111) (oneRows 58) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem inverse_row59 :
    digitsEq 111 (rowProduct (dRows 59) nRows 111) (oneRows 59) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem inverse_row60 :
    digitsEq 111 (rowProduct (dRows 60) nRows 111) (oneRows 60) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem inverse_row61 :
    digitsEq 111 (rowProduct (dRows 61) nRows 111) (oneRows 61) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem inverse_row62 :
    digitsEq 111 (rowProduct (dRows 62) nRows 111) (oneRows 62) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem inverse_row63 :
    digitsEq 111 (rowProduct (dRows 63) nRows 111) (oneRows 63) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem inverse_row64 :
    digitsEq 111 (rowProduct (dRows 64) nRows 111) (oneRows 64) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem inverse_row65 :
    digitsEq 111 (rowProduct (dRows 65) nRows 111) (oneRows 65) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem inverse_row66 :
    digitsEq 111 (rowProduct (dRows 66) nRows 111) (oneRows 66) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem inverse_row67 :
    digitsEq 111 (rowProduct (dRows 67) nRows 111) (oneRows 67) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem inverse_row68 :
    digitsEq 111 (rowProduct (dRows 68) nRows 111) (oneRows 68) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem inverse_row69 :
    digitsEq 111 (rowProduct (dRows 69) nRows 111) (oneRows 69) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem inverse_row70 :
    digitsEq 111 (rowProduct (dRows 70) nRows 111) (oneRows 70) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem inverse_row71 :
    digitsEq 111 (rowProduct (dRows 71) nRows 111) (oneRows 71) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem inverse_row72 :
    digitsEq 111 (rowProduct (dRows 72) nRows 111) (oneRows 72) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem inverse_row73 :
    digitsEq 111 (rowProduct (dRows 73) nRows 111) (oneRows 73) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem inverse_row74 :
    digitsEq 111 (rowProduct (dRows 74) nRows 111) (oneRows 74) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem inverse_row75 :
    digitsEq 111 (rowProduct (dRows 75) nRows 111) (oneRows 75) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem inverse_row76 :
    digitsEq 111 (rowProduct (dRows 76) nRows 111) (oneRows 76) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem inverse_row77 :
    digitsEq 111 (rowProduct (dRows 77) nRows 111) (oneRows 77) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem inverse_row78 :
    digitsEq 111 (rowProduct (dRows 78) nRows 111) (oneRows 78) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem inverse_row79 :
    digitsEq 111 (rowProduct (dRows 79) nRows 111) (oneRows 79) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem inverse_row80 :
    digitsEq 111 (rowProduct (dRows 80) nRows 111) (oneRows 80) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem inverse_row81 :
    digitsEq 111 (rowProduct (dRows 81) nRows 111) (oneRows 81) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem inverse_row82 :
    digitsEq 111 (rowProduct (dRows 82) nRows 111) (oneRows 82) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem inverse_row83 :
    digitsEq 111 (rowProduct (dRows 83) nRows 111) (oneRows 83) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem inverse_row84 :
    digitsEq 111 (rowProduct (dRows 84) nRows 111) (oneRows 84) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem inverse_row85 :
    digitsEq 111 (rowProduct (dRows 85) nRows 111) (oneRows 85) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem inverse_row86 :
    digitsEq 111 (rowProduct (dRows 86) nRows 111) (oneRows 86) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem inverse_row87 :
    digitsEq 111 (rowProduct (dRows 87) nRows 111) (oneRows 87) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem inverse_row88 :
    digitsEq 111 (rowProduct (dRows 88) nRows 111) (oneRows 88) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem inverse_row89 :
    digitsEq 111 (rowProduct (dRows 89) nRows 111) (oneRows 89) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem inverse_row90 :
    digitsEq 111 (rowProduct (dRows 90) nRows 111) (oneRows 90) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem inverse_row91 :
    digitsEq 111 (rowProduct (dRows 91) nRows 111) (oneRows 91) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem inverse_row92 :
    digitsEq 111 (rowProduct (dRows 92) nRows 111) (oneRows 92) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem inverse_row93 :
    digitsEq 111 (rowProduct (dRows 93) nRows 111) (oneRows 93) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem inverse_row94 :
    digitsEq 111 (rowProduct (dRows 94) nRows 111) (oneRows 94) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem inverse_row95 :
    digitsEq 111 (rowProduct (dRows 95) nRows 111) (oneRows 95) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem inverse_row96 :
    digitsEq 111 (rowProduct (dRows 96) nRows 111) (oneRows 96) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem inverse_row97 :
    digitsEq 111 (rowProduct (dRows 97) nRows 111) (oneRows 97) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem inverse_row98 :
    digitsEq 111 (rowProduct (dRows 98) nRows 111) (oneRows 98) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem inverse_row99 :
    digitsEq 111 (rowProduct (dRows 99) nRows 111) (oneRows 99) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem inverse_row100 :
    digitsEq 111 (rowProduct (dRows 100) nRows 111) (oneRows 100) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem inverse_row101 :
    digitsEq 111 (rowProduct (dRows 101) nRows 111) (oneRows 101) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem inverse_row102 :
    digitsEq 111 (rowProduct (dRows 102) nRows 111) (oneRows 102) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem inverse_row103 :
    digitsEq 111 (rowProduct (dRows 103) nRows 111) (oneRows 103) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem inverse_row104 :
    digitsEq 111 (rowProduct (dRows 104) nRows 111) (oneRows 104) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem inverse_row105 :
    digitsEq 111 (rowProduct (dRows 105) nRows 111) (oneRows 105) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem inverse_row106 :
    digitsEq 111 (rowProduct (dRows 106) nRows 111) (oneRows 106) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem inverse_row107 :
    digitsEq 111 (rowProduct (dRows 107) nRows 111) (oneRows 107) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem inverse_row108 :
    digitsEq 111 (rowProduct (dRows 108) nRows 111) (oneRows 108) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem inverse_row109 :
    digitsEq 111 (rowProduct (dRows 109) nRows 111) (oneRows 109) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem inverse_row110 :
    digitsEq 111 (rowProduct (dRows 110) nRows 111) (oneRows 110) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem inverse_rows : ∀ i,
    digitsEq 111 (rowProduct (dRows i) nRows 111) (oneRows i) = true :=
  (Fin.cases inverse_row0
    (Fin.cases inverse_row1
    (Fin.cases inverse_row2
    (Fin.cases inverse_row3
    (Fin.cases inverse_row4
    (Fin.cases inverse_row5
    (Fin.cases inverse_row6
    (Fin.cases inverse_row7
    (Fin.cases inverse_row8
    (Fin.cases inverse_row9
    (Fin.cases inverse_row10
    (Fin.cases inverse_row11
    (Fin.cases inverse_row12
    (Fin.cases inverse_row13
    (Fin.cases inverse_row14
    (Fin.cases inverse_row15
    (Fin.cases inverse_row16
    (Fin.cases inverse_row17
    (Fin.cases inverse_row18
    (Fin.cases inverse_row19
    (Fin.cases inverse_row20
    (Fin.cases inverse_row21
    (Fin.cases inverse_row22
    (Fin.cases inverse_row23
    (Fin.cases inverse_row24
    (Fin.cases inverse_row25
    (Fin.cases inverse_row26
    (Fin.cases inverse_row27
    (Fin.cases inverse_row28
    (Fin.cases inverse_row29
    (Fin.cases inverse_row30
    (Fin.cases inverse_row31
    (Fin.cases inverse_row32
    (Fin.cases inverse_row33
    (Fin.cases inverse_row34
    (Fin.cases inverse_row35
    (Fin.cases inverse_row36
    (Fin.cases inverse_row37
    (Fin.cases inverse_row38
    (Fin.cases inverse_row39
    (Fin.cases inverse_row40
    (Fin.cases inverse_row41
    (Fin.cases inverse_row42
    (Fin.cases inverse_row43
    (Fin.cases inverse_row44
    (Fin.cases inverse_row45
    (Fin.cases inverse_row46
    (Fin.cases inverse_row47
    (Fin.cases inverse_row48
    (Fin.cases inverse_row49
    (Fin.cases inverse_row50
    (Fin.cases inverse_row51
    (Fin.cases inverse_row52
    (Fin.cases inverse_row53
    (Fin.cases inverse_row54
    (Fin.cases inverse_row55
    (Fin.cases inverse_row56
    (Fin.cases inverse_row57
    (Fin.cases inverse_row58
    (Fin.cases inverse_row59
    (Fin.cases inverse_row60
    (Fin.cases inverse_row61
    (Fin.cases inverse_row62
    (Fin.cases inverse_row63
    (Fin.cases inverse_row64
    (Fin.cases inverse_row65
    (Fin.cases inverse_row66
    (Fin.cases inverse_row67
    (Fin.cases inverse_row68
    (Fin.cases inverse_row69
    (Fin.cases inverse_row70
    (Fin.cases inverse_row71
    (Fin.cases inverse_row72
    (Fin.cases inverse_row73
    (Fin.cases inverse_row74
    (Fin.cases inverse_row75
    (Fin.cases inverse_row76
    (Fin.cases inverse_row77
    (Fin.cases inverse_row78
    (Fin.cases inverse_row79
    (Fin.cases inverse_row80
    (Fin.cases inverse_row81
    (Fin.cases inverse_row82
    (Fin.cases inverse_row83
    (Fin.cases inverse_row84
    (Fin.cases inverse_row85
    (Fin.cases inverse_row86
    (Fin.cases inverse_row87
    (Fin.cases inverse_row88
    (Fin.cases inverse_row89
    (Fin.cases inverse_row90
    (Fin.cases inverse_row91
    (Fin.cases inverse_row92
    (Fin.cases inverse_row93
    (Fin.cases inverse_row94
    (Fin.cases inverse_row95
    (Fin.cases inverse_row96
    (Fin.cases inverse_row97
    (Fin.cases inverse_row98
    (Fin.cases inverse_row99
    (Fin.cases inverse_row100
    (Fin.cases inverse_row101
    (Fin.cases inverse_row102
    (Fin.cases inverse_row103
    (Fin.cases inverse_row104
    (Fin.cases inverse_row105
    (Fin.cases inverse_row106
    (Fin.cases inverse_row107
    (Fin.cases inverse_row108
    (Fin.cases inverse_row109
    (Fin.cases inverse_row110
    (fun i => Fin.elim0 i))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

/-- The candidate inverse is a left inverse in the actual matrix algebra. -/
public theorem inverse_mul : dMatrix * nMatrix = 1 :=
  (decode_mul _ _ _ d_small n_small inverse_rows).trans oneMatrix_eq

end Lyons.SimplicityCertificate.LocalCommutant.Kernel
