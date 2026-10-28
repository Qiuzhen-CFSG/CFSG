module

public import Theory.SpecificGroups.Lyons.Atlas111InvolutionLocalCommutant.Kernel.Polynomial.Family

/-!
# Weighted word rows

For each output row, the corresponding rows of all 111 words form a matrix.
Multiplying the packed coefficient vector by that matrix gives the weighted row.

Candidate generation and source attribution: `Kernel/source/GenerateKernel.py`
and `Kernel/source/README.md`. Every numerical assertion is checked in Lean.
-/

namespace Lyons.SimplicityCertificate.LocalCommutant.Kernel

open Atlas111WordCertificate

set_option Elab.async false

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem weighted_row0 :
    digitsEq 111 (rowProduct qPacked (fun k => wordRows k 0) 111) (sumRows 0) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem weighted_row1 :
    digitsEq 111 (rowProduct qPacked (fun k => wordRows k 1) 111) (sumRows 1) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem weighted_row2 :
    digitsEq 111 (rowProduct qPacked (fun k => wordRows k 2) 111) (sumRows 2) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem weighted_row3 :
    digitsEq 111 (rowProduct qPacked (fun k => wordRows k 3) 111) (sumRows 3) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem weighted_row4 :
    digitsEq 111 (rowProduct qPacked (fun k => wordRows k 4) 111) (sumRows 4) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem weighted_row5 :
    digitsEq 111 (rowProduct qPacked (fun k => wordRows k 5) 111) (sumRows 5) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem weighted_row6 :
    digitsEq 111 (rowProduct qPacked (fun k => wordRows k 6) 111) (sumRows 6) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem weighted_row7 :
    digitsEq 111 (rowProduct qPacked (fun k => wordRows k 7) 111) (sumRows 7) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem weighted_row8 :
    digitsEq 111 (rowProduct qPacked (fun k => wordRows k 8) 111) (sumRows 8) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem weighted_row9 :
    digitsEq 111 (rowProduct qPacked (fun k => wordRows k 9) 111) (sumRows 9) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem weighted_row10 :
    digitsEq 111 (rowProduct qPacked (fun k => wordRows k 10) 111) (sumRows 10) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem weighted_row11 :
    digitsEq 111 (rowProduct qPacked (fun k => wordRows k 11) 111) (sumRows 11) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem weighted_row12 :
    digitsEq 111 (rowProduct qPacked (fun k => wordRows k 12) 111) (sumRows 12) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem weighted_row13 :
    digitsEq 111 (rowProduct qPacked (fun k => wordRows k 13) 111) (sumRows 13) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem weighted_row14 :
    digitsEq 111 (rowProduct qPacked (fun k => wordRows k 14) 111) (sumRows 14) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem weighted_row15 :
    digitsEq 111 (rowProduct qPacked (fun k => wordRows k 15) 111) (sumRows 15) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem weighted_row16 :
    digitsEq 111 (rowProduct qPacked (fun k => wordRows k 16) 111) (sumRows 16) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem weighted_row17 :
    digitsEq 111 (rowProduct qPacked (fun k => wordRows k 17) 111) (sumRows 17) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem weighted_row18 :
    digitsEq 111 (rowProduct qPacked (fun k => wordRows k 18) 111) (sumRows 18) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem weighted_row19 :
    digitsEq 111 (rowProduct qPacked (fun k => wordRows k 19) 111) (sumRows 19) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem weighted_row20 :
    digitsEq 111 (rowProduct qPacked (fun k => wordRows k 20) 111) (sumRows 20) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem weighted_row21 :
    digitsEq 111 (rowProduct qPacked (fun k => wordRows k 21) 111) (sumRows 21) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem weighted_row22 :
    digitsEq 111 (rowProduct qPacked (fun k => wordRows k 22) 111) (sumRows 22) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem weighted_row23 :
    digitsEq 111 (rowProduct qPacked (fun k => wordRows k 23) 111) (sumRows 23) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem weighted_row24 :
    digitsEq 111 (rowProduct qPacked (fun k => wordRows k 24) 111) (sumRows 24) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem weighted_row25 :
    digitsEq 111 (rowProduct qPacked (fun k => wordRows k 25) 111) (sumRows 25) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem weighted_row26 :
    digitsEq 111 (rowProduct qPacked (fun k => wordRows k 26) 111) (sumRows 26) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem weighted_row27 :
    digitsEq 111 (rowProduct qPacked (fun k => wordRows k 27) 111) (sumRows 27) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem weighted_row28 :
    digitsEq 111 (rowProduct qPacked (fun k => wordRows k 28) 111) (sumRows 28) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem weighted_row29 :
    digitsEq 111 (rowProduct qPacked (fun k => wordRows k 29) 111) (sumRows 29) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem weighted_row30 :
    digitsEq 111 (rowProduct qPacked (fun k => wordRows k 30) 111) (sumRows 30) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem weighted_row31 :
    digitsEq 111 (rowProduct qPacked (fun k => wordRows k 31) 111) (sumRows 31) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem weighted_row32 :
    digitsEq 111 (rowProduct qPacked (fun k => wordRows k 32) 111) (sumRows 32) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem weighted_row33 :
    digitsEq 111 (rowProduct qPacked (fun k => wordRows k 33) 111) (sumRows 33) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem weighted_row34 :
    digitsEq 111 (rowProduct qPacked (fun k => wordRows k 34) 111) (sumRows 34) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem weighted_row35 :
    digitsEq 111 (rowProduct qPacked (fun k => wordRows k 35) 111) (sumRows 35) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem weighted_row36 :
    digitsEq 111 (rowProduct qPacked (fun k => wordRows k 36) 111) (sumRows 36) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem weighted_row37 :
    digitsEq 111 (rowProduct qPacked (fun k => wordRows k 37) 111) (sumRows 37) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem weighted_row38 :
    digitsEq 111 (rowProduct qPacked (fun k => wordRows k 38) 111) (sumRows 38) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem weighted_row39 :
    digitsEq 111 (rowProduct qPacked (fun k => wordRows k 39) 111) (sumRows 39) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem weighted_row40 :
    digitsEq 111 (rowProduct qPacked (fun k => wordRows k 40) 111) (sumRows 40) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem weighted_row41 :
    digitsEq 111 (rowProduct qPacked (fun k => wordRows k 41) 111) (sumRows 41) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem weighted_row42 :
    digitsEq 111 (rowProduct qPacked (fun k => wordRows k 42) 111) (sumRows 42) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem weighted_row43 :
    digitsEq 111 (rowProduct qPacked (fun k => wordRows k 43) 111) (sumRows 43) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem weighted_row44 :
    digitsEq 111 (rowProduct qPacked (fun k => wordRows k 44) 111) (sumRows 44) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem weighted_row45 :
    digitsEq 111 (rowProduct qPacked (fun k => wordRows k 45) 111) (sumRows 45) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem weighted_row46 :
    digitsEq 111 (rowProduct qPacked (fun k => wordRows k 46) 111) (sumRows 46) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem weighted_row47 :
    digitsEq 111 (rowProduct qPacked (fun k => wordRows k 47) 111) (sumRows 47) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem weighted_row48 :
    digitsEq 111 (rowProduct qPacked (fun k => wordRows k 48) 111) (sumRows 48) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem weighted_row49 :
    digitsEq 111 (rowProduct qPacked (fun k => wordRows k 49) 111) (sumRows 49) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem weighted_row50 :
    digitsEq 111 (rowProduct qPacked (fun k => wordRows k 50) 111) (sumRows 50) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem weighted_row51 :
    digitsEq 111 (rowProduct qPacked (fun k => wordRows k 51) 111) (sumRows 51) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem weighted_row52 :
    digitsEq 111 (rowProduct qPacked (fun k => wordRows k 52) 111) (sumRows 52) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem weighted_row53 :
    digitsEq 111 (rowProduct qPacked (fun k => wordRows k 53) 111) (sumRows 53) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem weighted_row54 :
    digitsEq 111 (rowProduct qPacked (fun k => wordRows k 54) 111) (sumRows 54) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem weighted_row55 :
    digitsEq 111 (rowProduct qPacked (fun k => wordRows k 55) 111) (sumRows 55) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem weighted_row56 :
    digitsEq 111 (rowProduct qPacked (fun k => wordRows k 56) 111) (sumRows 56) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem weighted_row57 :
    digitsEq 111 (rowProduct qPacked (fun k => wordRows k 57) 111) (sumRows 57) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem weighted_row58 :
    digitsEq 111 (rowProduct qPacked (fun k => wordRows k 58) 111) (sumRows 58) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem weighted_row59 :
    digitsEq 111 (rowProduct qPacked (fun k => wordRows k 59) 111) (sumRows 59) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem weighted_row60 :
    digitsEq 111 (rowProduct qPacked (fun k => wordRows k 60) 111) (sumRows 60) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem weighted_row61 :
    digitsEq 111 (rowProduct qPacked (fun k => wordRows k 61) 111) (sumRows 61) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem weighted_row62 :
    digitsEq 111 (rowProduct qPacked (fun k => wordRows k 62) 111) (sumRows 62) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem weighted_row63 :
    digitsEq 111 (rowProduct qPacked (fun k => wordRows k 63) 111) (sumRows 63) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem weighted_row64 :
    digitsEq 111 (rowProduct qPacked (fun k => wordRows k 64) 111) (sumRows 64) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem weighted_row65 :
    digitsEq 111 (rowProduct qPacked (fun k => wordRows k 65) 111) (sumRows 65) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem weighted_row66 :
    digitsEq 111 (rowProduct qPacked (fun k => wordRows k 66) 111) (sumRows 66) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem weighted_row67 :
    digitsEq 111 (rowProduct qPacked (fun k => wordRows k 67) 111) (sumRows 67) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem weighted_row68 :
    digitsEq 111 (rowProduct qPacked (fun k => wordRows k 68) 111) (sumRows 68) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem weighted_row69 :
    digitsEq 111 (rowProduct qPacked (fun k => wordRows k 69) 111) (sumRows 69) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem weighted_row70 :
    digitsEq 111 (rowProduct qPacked (fun k => wordRows k 70) 111) (sumRows 70) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem weighted_row71 :
    digitsEq 111 (rowProduct qPacked (fun k => wordRows k 71) 111) (sumRows 71) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem weighted_row72 :
    digitsEq 111 (rowProduct qPacked (fun k => wordRows k 72) 111) (sumRows 72) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem weighted_row73 :
    digitsEq 111 (rowProduct qPacked (fun k => wordRows k 73) 111) (sumRows 73) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem weighted_row74 :
    digitsEq 111 (rowProduct qPacked (fun k => wordRows k 74) 111) (sumRows 74) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem weighted_row75 :
    digitsEq 111 (rowProduct qPacked (fun k => wordRows k 75) 111) (sumRows 75) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem weighted_row76 :
    digitsEq 111 (rowProduct qPacked (fun k => wordRows k 76) 111) (sumRows 76) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem weighted_row77 :
    digitsEq 111 (rowProduct qPacked (fun k => wordRows k 77) 111) (sumRows 77) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem weighted_row78 :
    digitsEq 111 (rowProduct qPacked (fun k => wordRows k 78) 111) (sumRows 78) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem weighted_row79 :
    digitsEq 111 (rowProduct qPacked (fun k => wordRows k 79) 111) (sumRows 79) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem weighted_row80 :
    digitsEq 111 (rowProduct qPacked (fun k => wordRows k 80) 111) (sumRows 80) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem weighted_row81 :
    digitsEq 111 (rowProduct qPacked (fun k => wordRows k 81) 111) (sumRows 81) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem weighted_row82 :
    digitsEq 111 (rowProduct qPacked (fun k => wordRows k 82) 111) (sumRows 82) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem weighted_row83 :
    digitsEq 111 (rowProduct qPacked (fun k => wordRows k 83) 111) (sumRows 83) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem weighted_row84 :
    digitsEq 111 (rowProduct qPacked (fun k => wordRows k 84) 111) (sumRows 84) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem weighted_row85 :
    digitsEq 111 (rowProduct qPacked (fun k => wordRows k 85) 111) (sumRows 85) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem weighted_row86 :
    digitsEq 111 (rowProduct qPacked (fun k => wordRows k 86) 111) (sumRows 86) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem weighted_row87 :
    digitsEq 111 (rowProduct qPacked (fun k => wordRows k 87) 111) (sumRows 87) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem weighted_row88 :
    digitsEq 111 (rowProduct qPacked (fun k => wordRows k 88) 111) (sumRows 88) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem weighted_row89 :
    digitsEq 111 (rowProduct qPacked (fun k => wordRows k 89) 111) (sumRows 89) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem weighted_row90 :
    digitsEq 111 (rowProduct qPacked (fun k => wordRows k 90) 111) (sumRows 90) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem weighted_row91 :
    digitsEq 111 (rowProduct qPacked (fun k => wordRows k 91) 111) (sumRows 91) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem weighted_row92 :
    digitsEq 111 (rowProduct qPacked (fun k => wordRows k 92) 111) (sumRows 92) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem weighted_row93 :
    digitsEq 111 (rowProduct qPacked (fun k => wordRows k 93) 111) (sumRows 93) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem weighted_row94 :
    digitsEq 111 (rowProduct qPacked (fun k => wordRows k 94) 111) (sumRows 94) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem weighted_row95 :
    digitsEq 111 (rowProduct qPacked (fun k => wordRows k 95) 111) (sumRows 95) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem weighted_row96 :
    digitsEq 111 (rowProduct qPacked (fun k => wordRows k 96) 111) (sumRows 96) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem weighted_row97 :
    digitsEq 111 (rowProduct qPacked (fun k => wordRows k 97) 111) (sumRows 97) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem weighted_row98 :
    digitsEq 111 (rowProduct qPacked (fun k => wordRows k 98) 111) (sumRows 98) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem weighted_row99 :
    digitsEq 111 (rowProduct qPacked (fun k => wordRows k 99) 111) (sumRows 99) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem weighted_row100 :
    digitsEq 111 (rowProduct qPacked (fun k => wordRows k 100) 111) (sumRows 100) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem weighted_row101 :
    digitsEq 111 (rowProduct qPacked (fun k => wordRows k 101) 111) (sumRows 101) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem weighted_row102 :
    digitsEq 111 (rowProduct qPacked (fun k => wordRows k 102) 111) (sumRows 102) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem weighted_row103 :
    digitsEq 111 (rowProduct qPacked (fun k => wordRows k 103) 111) (sumRows 103) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem weighted_row104 :
    digitsEq 111 (rowProduct qPacked (fun k => wordRows k 104) 111) (sumRows 104) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem weighted_row105 :
    digitsEq 111 (rowProduct qPacked (fun k => wordRows k 105) 111) (sumRows 105) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem weighted_row106 :
    digitsEq 111 (rowProduct qPacked (fun k => wordRows k 106) 111) (sumRows 106) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem weighted_row107 :
    digitsEq 111 (rowProduct qPacked (fun k => wordRows k 107) 111) (sumRows 107) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem weighted_row108 :
    digitsEq 111 (rowProduct qPacked (fun k => wordRows k 108) 111) (sumRows 108) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem weighted_row109 :
    digitsEq 111 (rowProduct qPacked (fun k => wordRows k 109) 111) (sumRows 109) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem weighted_row110 :
    digitsEq 111 (rowProduct qPacked (fun k => wordRows k 110) 111) (sumRows 110) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
public theorem weighted_rows : ∀ i : Fin 111,
    digitsEq 111 (rowProduct qPacked (fun k => wordRows k i) 111) (sumRows i) = true :=
  (Fin.cases weighted_row0
    (Fin.cases weighted_row1
    (Fin.cases weighted_row2
    (Fin.cases weighted_row3
    (Fin.cases weighted_row4
    (Fin.cases weighted_row5
    (Fin.cases weighted_row6
    (Fin.cases weighted_row7
    (Fin.cases weighted_row8
    (Fin.cases weighted_row9
    (Fin.cases weighted_row10
    (Fin.cases weighted_row11
    (Fin.cases weighted_row12
    (Fin.cases weighted_row13
    (Fin.cases weighted_row14
    (Fin.cases weighted_row15
    (Fin.cases weighted_row16
    (Fin.cases weighted_row17
    (Fin.cases weighted_row18
    (Fin.cases weighted_row19
    (Fin.cases weighted_row20
    (Fin.cases weighted_row21
    (Fin.cases weighted_row22
    (Fin.cases weighted_row23
    (Fin.cases weighted_row24
    (Fin.cases weighted_row25
    (Fin.cases weighted_row26
    (Fin.cases weighted_row27
    (Fin.cases weighted_row28
    (Fin.cases weighted_row29
    (Fin.cases weighted_row30
    (Fin.cases weighted_row31
    (Fin.cases weighted_row32
    (Fin.cases weighted_row33
    (Fin.cases weighted_row34
    (Fin.cases weighted_row35
    (Fin.cases weighted_row36
    (Fin.cases weighted_row37
    (Fin.cases weighted_row38
    (Fin.cases weighted_row39
    (Fin.cases weighted_row40
    (Fin.cases weighted_row41
    (Fin.cases weighted_row42
    (Fin.cases weighted_row43
    (Fin.cases weighted_row44
    (Fin.cases weighted_row45
    (Fin.cases weighted_row46
    (Fin.cases weighted_row47
    (Fin.cases weighted_row48
    (Fin.cases weighted_row49
    (Fin.cases weighted_row50
    (Fin.cases weighted_row51
    (Fin.cases weighted_row52
    (Fin.cases weighted_row53
    (Fin.cases weighted_row54
    (Fin.cases weighted_row55
    (Fin.cases weighted_row56
    (Fin.cases weighted_row57
    (Fin.cases weighted_row58
    (Fin.cases weighted_row59
    (Fin.cases weighted_row60
    (Fin.cases weighted_row61
    (Fin.cases weighted_row62
    (Fin.cases weighted_row63
    (Fin.cases weighted_row64
    (Fin.cases weighted_row65
    (Fin.cases weighted_row66
    (Fin.cases weighted_row67
    (Fin.cases weighted_row68
    (Fin.cases weighted_row69
    (Fin.cases weighted_row70
    (Fin.cases weighted_row71
    (Fin.cases weighted_row72
    (Fin.cases weighted_row73
    (Fin.cases weighted_row74
    (Fin.cases weighted_row75
    (Fin.cases weighted_row76
    (Fin.cases weighted_row77
    (Fin.cases weighted_row78
    (Fin.cases weighted_row79
    (Fin.cases weighted_row80
    (Fin.cases weighted_row81
    (Fin.cases weighted_row82
    (Fin.cases weighted_row83
    (Fin.cases weighted_row84
    (Fin.cases weighted_row85
    (Fin.cases weighted_row86
    (Fin.cases weighted_row87
    (Fin.cases weighted_row88
    (Fin.cases weighted_row89
    (Fin.cases weighted_row90
    (Fin.cases weighted_row91
    (Fin.cases weighted_row92
    (Fin.cases weighted_row93
    (Fin.cases weighted_row94
    (Fin.cases weighted_row95
    (Fin.cases weighted_row96
    (Fin.cases weighted_row97
    (Fin.cases weighted_row98
    (Fin.cases weighted_row99
    (Fin.cases weighted_row100
    (Fin.cases weighted_row101
    (Fin.cases weighted_row102
    (Fin.cases weighted_row103
    (Fin.cases weighted_row104
    (Fin.cases weighted_row105
    (Fin.cases weighted_row106
    (Fin.cases weighted_row107
    (Fin.cases weighted_row108
    (Fin.cases weighted_row109
    (Fin.cases weighted_row110
    (fun i => Fin.elim0 i))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

end Lyons.SimplicityCertificate.LocalCommutant.Kernel
