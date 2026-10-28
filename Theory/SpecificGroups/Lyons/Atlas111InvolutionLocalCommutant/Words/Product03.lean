module

public import Theory.SpecificGroups.Lyons.Atlas111InvolutionLocalCommutant.Words.Data

/-!
# Involution word multiplication: r6 times r5

The carry-free arithmetic soundness theorem converts the 111
closed row checks into the displayed matrix identity.

Source and reproducible candidate generation:
`Atlas111InvolutionLocalCommutant/Words/source/GenerateWords.py` and the attributed
original matrices in `Atlas111Source/`. All checks run in Lean's kernel.
-/

namespace Lyons.SimplicityCertificate.LocalCommutant.Words

open Atlas111WordCertificate

set_option Elab.async false

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r8_row0 :
    digitsEq 111 (rowProduct (r6Rows 0) r5Rows 111) (r8Rows 0)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r8_row1 :
    digitsEq 111 (rowProduct (r6Rows 1) r5Rows 111) (r8Rows 1)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r8_row2 :
    digitsEq 111 (rowProduct (r6Rows 2) r5Rows 111) (r8Rows 2)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r8_row3 :
    digitsEq 111 (rowProduct (r6Rows 3) r5Rows 111) (r8Rows 3)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r8_row4 :
    digitsEq 111 (rowProduct (r6Rows 4) r5Rows 111) (r8Rows 4)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r8_row5 :
    digitsEq 111 (rowProduct (r6Rows 5) r5Rows 111) (r8Rows 5)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r8_row6 :
    digitsEq 111 (rowProduct (r6Rows 6) r5Rows 111) (r8Rows 6)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r8_row7 :
    digitsEq 111 (rowProduct (r6Rows 7) r5Rows 111) (r8Rows 7)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r8_row8 :
    digitsEq 111 (rowProduct (r6Rows 8) r5Rows 111) (r8Rows 8)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r8_row9 :
    digitsEq 111 (rowProduct (r6Rows 9) r5Rows 111) (r8Rows 9)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r8_row10 :
    digitsEq 111 (rowProduct (r6Rows 10) r5Rows 111) (r8Rows 10)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r8_row11 :
    digitsEq 111 (rowProduct (r6Rows 11) r5Rows 111) (r8Rows 11)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r8_row12 :
    digitsEq 111 (rowProduct (r6Rows 12) r5Rows 111) (r8Rows 12)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r8_row13 :
    digitsEq 111 (rowProduct (r6Rows 13) r5Rows 111) (r8Rows 13)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r8_row14 :
    digitsEq 111 (rowProduct (r6Rows 14) r5Rows 111) (r8Rows 14)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r8_row15 :
    digitsEq 111 (rowProduct (r6Rows 15) r5Rows 111) (r8Rows 15)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r8_row16 :
    digitsEq 111 (rowProduct (r6Rows 16) r5Rows 111) (r8Rows 16)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r8_row17 :
    digitsEq 111 (rowProduct (r6Rows 17) r5Rows 111) (r8Rows 17)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r8_row18 :
    digitsEq 111 (rowProduct (r6Rows 18) r5Rows 111) (r8Rows 18)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r8_row19 :
    digitsEq 111 (rowProduct (r6Rows 19) r5Rows 111) (r8Rows 19)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r8_row20 :
    digitsEq 111 (rowProduct (r6Rows 20) r5Rows 111) (r8Rows 20)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r8_row21 :
    digitsEq 111 (rowProduct (r6Rows 21) r5Rows 111) (r8Rows 21)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r8_row22 :
    digitsEq 111 (rowProduct (r6Rows 22) r5Rows 111) (r8Rows 22)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r8_row23 :
    digitsEq 111 (rowProduct (r6Rows 23) r5Rows 111) (r8Rows 23)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r8_row24 :
    digitsEq 111 (rowProduct (r6Rows 24) r5Rows 111) (r8Rows 24)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r8_row25 :
    digitsEq 111 (rowProduct (r6Rows 25) r5Rows 111) (r8Rows 25)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r8_row26 :
    digitsEq 111 (rowProduct (r6Rows 26) r5Rows 111) (r8Rows 26)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r8_row27 :
    digitsEq 111 (rowProduct (r6Rows 27) r5Rows 111) (r8Rows 27)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r8_row28 :
    digitsEq 111 (rowProduct (r6Rows 28) r5Rows 111) (r8Rows 28)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r8_row29 :
    digitsEq 111 (rowProduct (r6Rows 29) r5Rows 111) (r8Rows 29)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r8_row30 :
    digitsEq 111 (rowProduct (r6Rows 30) r5Rows 111) (r8Rows 30)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r8_row31 :
    digitsEq 111 (rowProduct (r6Rows 31) r5Rows 111) (r8Rows 31)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r8_row32 :
    digitsEq 111 (rowProduct (r6Rows 32) r5Rows 111) (r8Rows 32)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r8_row33 :
    digitsEq 111 (rowProduct (r6Rows 33) r5Rows 111) (r8Rows 33)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r8_row34 :
    digitsEq 111 (rowProduct (r6Rows 34) r5Rows 111) (r8Rows 34)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r8_row35 :
    digitsEq 111 (rowProduct (r6Rows 35) r5Rows 111) (r8Rows 35)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r8_row36 :
    digitsEq 111 (rowProduct (r6Rows 36) r5Rows 111) (r8Rows 36)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r8_row37 :
    digitsEq 111 (rowProduct (r6Rows 37) r5Rows 111) (r8Rows 37)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r8_row38 :
    digitsEq 111 (rowProduct (r6Rows 38) r5Rows 111) (r8Rows 38)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r8_row39 :
    digitsEq 111 (rowProduct (r6Rows 39) r5Rows 111) (r8Rows 39)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r8_row40 :
    digitsEq 111 (rowProduct (r6Rows 40) r5Rows 111) (r8Rows 40)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r8_row41 :
    digitsEq 111 (rowProduct (r6Rows 41) r5Rows 111) (r8Rows 41)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r8_row42 :
    digitsEq 111 (rowProduct (r6Rows 42) r5Rows 111) (r8Rows 42)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r8_row43 :
    digitsEq 111 (rowProduct (r6Rows 43) r5Rows 111) (r8Rows 43)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r8_row44 :
    digitsEq 111 (rowProduct (r6Rows 44) r5Rows 111) (r8Rows 44)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r8_row45 :
    digitsEq 111 (rowProduct (r6Rows 45) r5Rows 111) (r8Rows 45)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r8_row46 :
    digitsEq 111 (rowProduct (r6Rows 46) r5Rows 111) (r8Rows 46)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r8_row47 :
    digitsEq 111 (rowProduct (r6Rows 47) r5Rows 111) (r8Rows 47)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r8_row48 :
    digitsEq 111 (rowProduct (r6Rows 48) r5Rows 111) (r8Rows 48)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r8_row49 :
    digitsEq 111 (rowProduct (r6Rows 49) r5Rows 111) (r8Rows 49)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r8_row50 :
    digitsEq 111 (rowProduct (r6Rows 50) r5Rows 111) (r8Rows 50)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r8_row51 :
    digitsEq 111 (rowProduct (r6Rows 51) r5Rows 111) (r8Rows 51)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r8_row52 :
    digitsEq 111 (rowProduct (r6Rows 52) r5Rows 111) (r8Rows 52)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r8_row53 :
    digitsEq 111 (rowProduct (r6Rows 53) r5Rows 111) (r8Rows 53)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r8_row54 :
    digitsEq 111 (rowProduct (r6Rows 54) r5Rows 111) (r8Rows 54)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r8_row55 :
    digitsEq 111 (rowProduct (r6Rows 55) r5Rows 111) (r8Rows 55)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r8_row56 :
    digitsEq 111 (rowProduct (r6Rows 56) r5Rows 111) (r8Rows 56)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r8_row57 :
    digitsEq 111 (rowProduct (r6Rows 57) r5Rows 111) (r8Rows 57)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r8_row58 :
    digitsEq 111 (rowProduct (r6Rows 58) r5Rows 111) (r8Rows 58)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r8_row59 :
    digitsEq 111 (rowProduct (r6Rows 59) r5Rows 111) (r8Rows 59)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r8_row60 :
    digitsEq 111 (rowProduct (r6Rows 60) r5Rows 111) (r8Rows 60)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r8_row61 :
    digitsEq 111 (rowProduct (r6Rows 61) r5Rows 111) (r8Rows 61)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r8_row62 :
    digitsEq 111 (rowProduct (r6Rows 62) r5Rows 111) (r8Rows 62)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r8_row63 :
    digitsEq 111 (rowProduct (r6Rows 63) r5Rows 111) (r8Rows 63)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r8_row64 :
    digitsEq 111 (rowProduct (r6Rows 64) r5Rows 111) (r8Rows 64)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r8_row65 :
    digitsEq 111 (rowProduct (r6Rows 65) r5Rows 111) (r8Rows 65)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r8_row66 :
    digitsEq 111 (rowProduct (r6Rows 66) r5Rows 111) (r8Rows 66)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r8_row67 :
    digitsEq 111 (rowProduct (r6Rows 67) r5Rows 111) (r8Rows 67)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r8_row68 :
    digitsEq 111 (rowProduct (r6Rows 68) r5Rows 111) (r8Rows 68)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r8_row69 :
    digitsEq 111 (rowProduct (r6Rows 69) r5Rows 111) (r8Rows 69)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r8_row70 :
    digitsEq 111 (rowProduct (r6Rows 70) r5Rows 111) (r8Rows 70)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r8_row71 :
    digitsEq 111 (rowProduct (r6Rows 71) r5Rows 111) (r8Rows 71)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r8_row72 :
    digitsEq 111 (rowProduct (r6Rows 72) r5Rows 111) (r8Rows 72)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r8_row73 :
    digitsEq 111 (rowProduct (r6Rows 73) r5Rows 111) (r8Rows 73)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r8_row74 :
    digitsEq 111 (rowProduct (r6Rows 74) r5Rows 111) (r8Rows 74)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r8_row75 :
    digitsEq 111 (rowProduct (r6Rows 75) r5Rows 111) (r8Rows 75)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r8_row76 :
    digitsEq 111 (rowProduct (r6Rows 76) r5Rows 111) (r8Rows 76)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r8_row77 :
    digitsEq 111 (rowProduct (r6Rows 77) r5Rows 111) (r8Rows 77)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r8_row78 :
    digitsEq 111 (rowProduct (r6Rows 78) r5Rows 111) (r8Rows 78)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r8_row79 :
    digitsEq 111 (rowProduct (r6Rows 79) r5Rows 111) (r8Rows 79)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r8_row80 :
    digitsEq 111 (rowProduct (r6Rows 80) r5Rows 111) (r8Rows 80)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r8_row81 :
    digitsEq 111 (rowProduct (r6Rows 81) r5Rows 111) (r8Rows 81)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r8_row82 :
    digitsEq 111 (rowProduct (r6Rows 82) r5Rows 111) (r8Rows 82)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r8_row83 :
    digitsEq 111 (rowProduct (r6Rows 83) r5Rows 111) (r8Rows 83)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r8_row84 :
    digitsEq 111 (rowProduct (r6Rows 84) r5Rows 111) (r8Rows 84)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r8_row85 :
    digitsEq 111 (rowProduct (r6Rows 85) r5Rows 111) (r8Rows 85)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r8_row86 :
    digitsEq 111 (rowProduct (r6Rows 86) r5Rows 111) (r8Rows 86)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r8_row87 :
    digitsEq 111 (rowProduct (r6Rows 87) r5Rows 111) (r8Rows 87)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r8_row88 :
    digitsEq 111 (rowProduct (r6Rows 88) r5Rows 111) (r8Rows 88)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r8_row89 :
    digitsEq 111 (rowProduct (r6Rows 89) r5Rows 111) (r8Rows 89)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r8_row90 :
    digitsEq 111 (rowProduct (r6Rows 90) r5Rows 111) (r8Rows 90)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r8_row91 :
    digitsEq 111 (rowProduct (r6Rows 91) r5Rows 111) (r8Rows 91)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r8_row92 :
    digitsEq 111 (rowProduct (r6Rows 92) r5Rows 111) (r8Rows 92)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r8_row93 :
    digitsEq 111 (rowProduct (r6Rows 93) r5Rows 111) (r8Rows 93)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r8_row94 :
    digitsEq 111 (rowProduct (r6Rows 94) r5Rows 111) (r8Rows 94)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r8_row95 :
    digitsEq 111 (rowProduct (r6Rows 95) r5Rows 111) (r8Rows 95)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r8_row96 :
    digitsEq 111 (rowProduct (r6Rows 96) r5Rows 111) (r8Rows 96)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r8_row97 :
    digitsEq 111 (rowProduct (r6Rows 97) r5Rows 111) (r8Rows 97)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r8_row98 :
    digitsEq 111 (rowProduct (r6Rows 98) r5Rows 111) (r8Rows 98)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r8_row99 :
    digitsEq 111 (rowProduct (r6Rows 99) r5Rows 111) (r8Rows 99)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r8_row100 :
    digitsEq 111 (rowProduct (r6Rows 100) r5Rows 111) (r8Rows 100)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r8_row101 :
    digitsEq 111 (rowProduct (r6Rows 101) r5Rows 111) (r8Rows 101)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r8_row102 :
    digitsEq 111 (rowProduct (r6Rows 102) r5Rows 111) (r8Rows 102)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r8_row103 :
    digitsEq 111 (rowProduct (r6Rows 103) r5Rows 111) (r8Rows 103)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r8_row104 :
    digitsEq 111 (rowProduct (r6Rows 104) r5Rows 111) (r8Rows 104)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r8_row105 :
    digitsEq 111 (rowProduct (r6Rows 105) r5Rows 111) (r8Rows 105)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r8_row106 :
    digitsEq 111 (rowProduct (r6Rows 106) r5Rows 111) (r8Rows 106)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r8_row107 :
    digitsEq 111 (rowProduct (r6Rows 107) r5Rows 111) (r8Rows 107)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r8_row108 :
    digitsEq 111 (rowProduct (r6Rows 108) r5Rows 111) (r8Rows 108)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r8_row109 :
    digitsEq 111 (rowProduct (r6Rows 109) r5Rows 111) (r8Rows 109)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r8_row110 :
    digitsEq 111 (rowProduct (r6Rows 110) r5Rows 111) (r8Rows 110)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem r8_rows : ∀ i,
    digitsEq 111 (rowProduct (r6Rows i) r5Rows 111) (r8Rows i) = true :=
  (Fin.cases r8_row0
    (Fin.cases r8_row1
    (Fin.cases r8_row2
    (Fin.cases r8_row3
    (Fin.cases r8_row4
    (Fin.cases r8_row5
    (Fin.cases r8_row6
    (Fin.cases r8_row7
    (Fin.cases r8_row8
    (Fin.cases r8_row9
    (Fin.cases r8_row10
    (Fin.cases r8_row11
    (Fin.cases r8_row12
    (Fin.cases r8_row13
    (Fin.cases r8_row14
    (Fin.cases r8_row15
    (Fin.cases r8_row16
    (Fin.cases r8_row17
    (Fin.cases r8_row18
    (Fin.cases r8_row19
    (Fin.cases r8_row20
    (Fin.cases r8_row21
    (Fin.cases r8_row22
    (Fin.cases r8_row23
    (Fin.cases r8_row24
    (Fin.cases r8_row25
    (Fin.cases r8_row26
    (Fin.cases r8_row27
    (Fin.cases r8_row28
    (Fin.cases r8_row29
    (Fin.cases r8_row30
    (Fin.cases r8_row31
    (Fin.cases r8_row32
    (Fin.cases r8_row33
    (Fin.cases r8_row34
    (Fin.cases r8_row35
    (Fin.cases r8_row36
    (Fin.cases r8_row37
    (Fin.cases r8_row38
    (Fin.cases r8_row39
    (Fin.cases r8_row40
    (Fin.cases r8_row41
    (Fin.cases r8_row42
    (Fin.cases r8_row43
    (Fin.cases r8_row44
    (Fin.cases r8_row45
    (Fin.cases r8_row46
    (Fin.cases r8_row47
    (Fin.cases r8_row48
    (Fin.cases r8_row49
    (Fin.cases r8_row50
    (Fin.cases r8_row51
    (Fin.cases r8_row52
    (Fin.cases r8_row53
    (Fin.cases r8_row54
    (Fin.cases r8_row55
    (Fin.cases r8_row56
    (Fin.cases r8_row57
    (Fin.cases r8_row58
    (Fin.cases r8_row59
    (Fin.cases r8_row60
    (Fin.cases r8_row61
    (Fin.cases r8_row62
    (Fin.cases r8_row63
    (Fin.cases r8_row64
    (Fin.cases r8_row65
    (Fin.cases r8_row66
    (Fin.cases r8_row67
    (Fin.cases r8_row68
    (Fin.cases r8_row69
    (Fin.cases r8_row70
    (Fin.cases r8_row71
    (Fin.cases r8_row72
    (Fin.cases r8_row73
    (Fin.cases r8_row74
    (Fin.cases r8_row75
    (Fin.cases r8_row76
    (Fin.cases r8_row77
    (Fin.cases r8_row78
    (Fin.cases r8_row79
    (Fin.cases r8_row80
    (Fin.cases r8_row81
    (Fin.cases r8_row82
    (Fin.cases r8_row83
    (Fin.cases r8_row84
    (Fin.cases r8_row85
    (Fin.cases r8_row86
    (Fin.cases r8_row87
    (Fin.cases r8_row88
    (Fin.cases r8_row89
    (Fin.cases r8_row90
    (Fin.cases r8_row91
    (Fin.cases r8_row92
    (Fin.cases r8_row93
    (Fin.cases r8_row94
    (Fin.cases r8_row95
    (Fin.cases r8_row96
    (Fin.cases r8_row97
    (Fin.cases r8_row98
    (Fin.cases r8_row99
    (Fin.cases r8_row100
    (Fin.cases r8_row101
    (Fin.cases r8_row102
    (Fin.cases r8_row103
    (Fin.cases r8_row104
    (Fin.cases r8_row105
    (Fin.cases r8_row106
    (Fin.cases r8_row107
    (Fin.cases r8_row108
    (Fin.cases r8_row109
    (Fin.cases r8_row110
    (fun i => Fin.elim0 i))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

/-- Kernel-checked multiplication in the actual matrix algebra. -/
public theorem mul_r8 : r6Matrix * r5Matrix = r8Matrix :=
  decode_mul _ _ _ r6_small r5_small r8_rows

end Lyons.SimplicityCertificate.LocalCommutant.Words
