module

public import Theory.SpecificGroups.Lyons.Atlas111InvolutionLocalCommutant.Words.Data

/-!
# Involution word multiplication: ab times r8

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
private theorem r9_row0 :
    digitsEq 111 (rowProduct (abRows 0) r8Rows 111) (r9Rows 0)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r9_row1 :
    digitsEq 111 (rowProduct (abRows 1) r8Rows 111) (r9Rows 1)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r9_row2 :
    digitsEq 111 (rowProduct (abRows 2) r8Rows 111) (r9Rows 2)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r9_row3 :
    digitsEq 111 (rowProduct (abRows 3) r8Rows 111) (r9Rows 3)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r9_row4 :
    digitsEq 111 (rowProduct (abRows 4) r8Rows 111) (r9Rows 4)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r9_row5 :
    digitsEq 111 (rowProduct (abRows 5) r8Rows 111) (r9Rows 5)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r9_row6 :
    digitsEq 111 (rowProduct (abRows 6) r8Rows 111) (r9Rows 6)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r9_row7 :
    digitsEq 111 (rowProduct (abRows 7) r8Rows 111) (r9Rows 7)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r9_row8 :
    digitsEq 111 (rowProduct (abRows 8) r8Rows 111) (r9Rows 8)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r9_row9 :
    digitsEq 111 (rowProduct (abRows 9) r8Rows 111) (r9Rows 9)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r9_row10 :
    digitsEq 111 (rowProduct (abRows 10) r8Rows 111) (r9Rows 10)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r9_row11 :
    digitsEq 111 (rowProduct (abRows 11) r8Rows 111) (r9Rows 11)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r9_row12 :
    digitsEq 111 (rowProduct (abRows 12) r8Rows 111) (r9Rows 12)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r9_row13 :
    digitsEq 111 (rowProduct (abRows 13) r8Rows 111) (r9Rows 13)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r9_row14 :
    digitsEq 111 (rowProduct (abRows 14) r8Rows 111) (r9Rows 14)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r9_row15 :
    digitsEq 111 (rowProduct (abRows 15) r8Rows 111) (r9Rows 15)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r9_row16 :
    digitsEq 111 (rowProduct (abRows 16) r8Rows 111) (r9Rows 16)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r9_row17 :
    digitsEq 111 (rowProduct (abRows 17) r8Rows 111) (r9Rows 17)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r9_row18 :
    digitsEq 111 (rowProduct (abRows 18) r8Rows 111) (r9Rows 18)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r9_row19 :
    digitsEq 111 (rowProduct (abRows 19) r8Rows 111) (r9Rows 19)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r9_row20 :
    digitsEq 111 (rowProduct (abRows 20) r8Rows 111) (r9Rows 20)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r9_row21 :
    digitsEq 111 (rowProduct (abRows 21) r8Rows 111) (r9Rows 21)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r9_row22 :
    digitsEq 111 (rowProduct (abRows 22) r8Rows 111) (r9Rows 22)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r9_row23 :
    digitsEq 111 (rowProduct (abRows 23) r8Rows 111) (r9Rows 23)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r9_row24 :
    digitsEq 111 (rowProduct (abRows 24) r8Rows 111) (r9Rows 24)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r9_row25 :
    digitsEq 111 (rowProduct (abRows 25) r8Rows 111) (r9Rows 25)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r9_row26 :
    digitsEq 111 (rowProduct (abRows 26) r8Rows 111) (r9Rows 26)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r9_row27 :
    digitsEq 111 (rowProduct (abRows 27) r8Rows 111) (r9Rows 27)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r9_row28 :
    digitsEq 111 (rowProduct (abRows 28) r8Rows 111) (r9Rows 28)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r9_row29 :
    digitsEq 111 (rowProduct (abRows 29) r8Rows 111) (r9Rows 29)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r9_row30 :
    digitsEq 111 (rowProduct (abRows 30) r8Rows 111) (r9Rows 30)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r9_row31 :
    digitsEq 111 (rowProduct (abRows 31) r8Rows 111) (r9Rows 31)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r9_row32 :
    digitsEq 111 (rowProduct (abRows 32) r8Rows 111) (r9Rows 32)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r9_row33 :
    digitsEq 111 (rowProduct (abRows 33) r8Rows 111) (r9Rows 33)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r9_row34 :
    digitsEq 111 (rowProduct (abRows 34) r8Rows 111) (r9Rows 34)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r9_row35 :
    digitsEq 111 (rowProduct (abRows 35) r8Rows 111) (r9Rows 35)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r9_row36 :
    digitsEq 111 (rowProduct (abRows 36) r8Rows 111) (r9Rows 36)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r9_row37 :
    digitsEq 111 (rowProduct (abRows 37) r8Rows 111) (r9Rows 37)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r9_row38 :
    digitsEq 111 (rowProduct (abRows 38) r8Rows 111) (r9Rows 38)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r9_row39 :
    digitsEq 111 (rowProduct (abRows 39) r8Rows 111) (r9Rows 39)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r9_row40 :
    digitsEq 111 (rowProduct (abRows 40) r8Rows 111) (r9Rows 40)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r9_row41 :
    digitsEq 111 (rowProduct (abRows 41) r8Rows 111) (r9Rows 41)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r9_row42 :
    digitsEq 111 (rowProduct (abRows 42) r8Rows 111) (r9Rows 42)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r9_row43 :
    digitsEq 111 (rowProduct (abRows 43) r8Rows 111) (r9Rows 43)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r9_row44 :
    digitsEq 111 (rowProduct (abRows 44) r8Rows 111) (r9Rows 44)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r9_row45 :
    digitsEq 111 (rowProduct (abRows 45) r8Rows 111) (r9Rows 45)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r9_row46 :
    digitsEq 111 (rowProduct (abRows 46) r8Rows 111) (r9Rows 46)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r9_row47 :
    digitsEq 111 (rowProduct (abRows 47) r8Rows 111) (r9Rows 47)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r9_row48 :
    digitsEq 111 (rowProduct (abRows 48) r8Rows 111) (r9Rows 48)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r9_row49 :
    digitsEq 111 (rowProduct (abRows 49) r8Rows 111) (r9Rows 49)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r9_row50 :
    digitsEq 111 (rowProduct (abRows 50) r8Rows 111) (r9Rows 50)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r9_row51 :
    digitsEq 111 (rowProduct (abRows 51) r8Rows 111) (r9Rows 51)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r9_row52 :
    digitsEq 111 (rowProduct (abRows 52) r8Rows 111) (r9Rows 52)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r9_row53 :
    digitsEq 111 (rowProduct (abRows 53) r8Rows 111) (r9Rows 53)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r9_row54 :
    digitsEq 111 (rowProduct (abRows 54) r8Rows 111) (r9Rows 54)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r9_row55 :
    digitsEq 111 (rowProduct (abRows 55) r8Rows 111) (r9Rows 55)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r9_row56 :
    digitsEq 111 (rowProduct (abRows 56) r8Rows 111) (r9Rows 56)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r9_row57 :
    digitsEq 111 (rowProduct (abRows 57) r8Rows 111) (r9Rows 57)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r9_row58 :
    digitsEq 111 (rowProduct (abRows 58) r8Rows 111) (r9Rows 58)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r9_row59 :
    digitsEq 111 (rowProduct (abRows 59) r8Rows 111) (r9Rows 59)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r9_row60 :
    digitsEq 111 (rowProduct (abRows 60) r8Rows 111) (r9Rows 60)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r9_row61 :
    digitsEq 111 (rowProduct (abRows 61) r8Rows 111) (r9Rows 61)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r9_row62 :
    digitsEq 111 (rowProduct (abRows 62) r8Rows 111) (r9Rows 62)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r9_row63 :
    digitsEq 111 (rowProduct (abRows 63) r8Rows 111) (r9Rows 63)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r9_row64 :
    digitsEq 111 (rowProduct (abRows 64) r8Rows 111) (r9Rows 64)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r9_row65 :
    digitsEq 111 (rowProduct (abRows 65) r8Rows 111) (r9Rows 65)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r9_row66 :
    digitsEq 111 (rowProduct (abRows 66) r8Rows 111) (r9Rows 66)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r9_row67 :
    digitsEq 111 (rowProduct (abRows 67) r8Rows 111) (r9Rows 67)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r9_row68 :
    digitsEq 111 (rowProduct (abRows 68) r8Rows 111) (r9Rows 68)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r9_row69 :
    digitsEq 111 (rowProduct (abRows 69) r8Rows 111) (r9Rows 69)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r9_row70 :
    digitsEq 111 (rowProduct (abRows 70) r8Rows 111) (r9Rows 70)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r9_row71 :
    digitsEq 111 (rowProduct (abRows 71) r8Rows 111) (r9Rows 71)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r9_row72 :
    digitsEq 111 (rowProduct (abRows 72) r8Rows 111) (r9Rows 72)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r9_row73 :
    digitsEq 111 (rowProduct (abRows 73) r8Rows 111) (r9Rows 73)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r9_row74 :
    digitsEq 111 (rowProduct (abRows 74) r8Rows 111) (r9Rows 74)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r9_row75 :
    digitsEq 111 (rowProduct (abRows 75) r8Rows 111) (r9Rows 75)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r9_row76 :
    digitsEq 111 (rowProduct (abRows 76) r8Rows 111) (r9Rows 76)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r9_row77 :
    digitsEq 111 (rowProduct (abRows 77) r8Rows 111) (r9Rows 77)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r9_row78 :
    digitsEq 111 (rowProduct (abRows 78) r8Rows 111) (r9Rows 78)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r9_row79 :
    digitsEq 111 (rowProduct (abRows 79) r8Rows 111) (r9Rows 79)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r9_row80 :
    digitsEq 111 (rowProduct (abRows 80) r8Rows 111) (r9Rows 80)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r9_row81 :
    digitsEq 111 (rowProduct (abRows 81) r8Rows 111) (r9Rows 81)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r9_row82 :
    digitsEq 111 (rowProduct (abRows 82) r8Rows 111) (r9Rows 82)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r9_row83 :
    digitsEq 111 (rowProduct (abRows 83) r8Rows 111) (r9Rows 83)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r9_row84 :
    digitsEq 111 (rowProduct (abRows 84) r8Rows 111) (r9Rows 84)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r9_row85 :
    digitsEq 111 (rowProduct (abRows 85) r8Rows 111) (r9Rows 85)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r9_row86 :
    digitsEq 111 (rowProduct (abRows 86) r8Rows 111) (r9Rows 86)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r9_row87 :
    digitsEq 111 (rowProduct (abRows 87) r8Rows 111) (r9Rows 87)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r9_row88 :
    digitsEq 111 (rowProduct (abRows 88) r8Rows 111) (r9Rows 88)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r9_row89 :
    digitsEq 111 (rowProduct (abRows 89) r8Rows 111) (r9Rows 89)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r9_row90 :
    digitsEq 111 (rowProduct (abRows 90) r8Rows 111) (r9Rows 90)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r9_row91 :
    digitsEq 111 (rowProduct (abRows 91) r8Rows 111) (r9Rows 91)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r9_row92 :
    digitsEq 111 (rowProduct (abRows 92) r8Rows 111) (r9Rows 92)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r9_row93 :
    digitsEq 111 (rowProduct (abRows 93) r8Rows 111) (r9Rows 93)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r9_row94 :
    digitsEq 111 (rowProduct (abRows 94) r8Rows 111) (r9Rows 94)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r9_row95 :
    digitsEq 111 (rowProduct (abRows 95) r8Rows 111) (r9Rows 95)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r9_row96 :
    digitsEq 111 (rowProduct (abRows 96) r8Rows 111) (r9Rows 96)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r9_row97 :
    digitsEq 111 (rowProduct (abRows 97) r8Rows 111) (r9Rows 97)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r9_row98 :
    digitsEq 111 (rowProduct (abRows 98) r8Rows 111) (r9Rows 98)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r9_row99 :
    digitsEq 111 (rowProduct (abRows 99) r8Rows 111) (r9Rows 99)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r9_row100 :
    digitsEq 111 (rowProduct (abRows 100) r8Rows 111) (r9Rows 100)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r9_row101 :
    digitsEq 111 (rowProduct (abRows 101) r8Rows 111) (r9Rows 101)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r9_row102 :
    digitsEq 111 (rowProduct (abRows 102) r8Rows 111) (r9Rows 102)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r9_row103 :
    digitsEq 111 (rowProduct (abRows 103) r8Rows 111) (r9Rows 103)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r9_row104 :
    digitsEq 111 (rowProduct (abRows 104) r8Rows 111) (r9Rows 104)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r9_row105 :
    digitsEq 111 (rowProduct (abRows 105) r8Rows 111) (r9Rows 105)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r9_row106 :
    digitsEq 111 (rowProduct (abRows 106) r8Rows 111) (r9Rows 106)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r9_row107 :
    digitsEq 111 (rowProduct (abRows 107) r8Rows 111) (r9Rows 107)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r9_row108 :
    digitsEq 111 (rowProduct (abRows 108) r8Rows 111) (r9Rows 108)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r9_row109 :
    digitsEq 111 (rowProduct (abRows 109) r8Rows 111) (r9Rows 109)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r9_row110 :
    digitsEq 111 (rowProduct (abRows 110) r8Rows 111) (r9Rows 110)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem r9_rows : ∀ i,
    digitsEq 111 (rowProduct (abRows i) r8Rows 111) (r9Rows i) = true :=
  (Fin.cases r9_row0
    (Fin.cases r9_row1
    (Fin.cases r9_row2
    (Fin.cases r9_row3
    (Fin.cases r9_row4
    (Fin.cases r9_row5
    (Fin.cases r9_row6
    (Fin.cases r9_row7
    (Fin.cases r9_row8
    (Fin.cases r9_row9
    (Fin.cases r9_row10
    (Fin.cases r9_row11
    (Fin.cases r9_row12
    (Fin.cases r9_row13
    (Fin.cases r9_row14
    (Fin.cases r9_row15
    (Fin.cases r9_row16
    (Fin.cases r9_row17
    (Fin.cases r9_row18
    (Fin.cases r9_row19
    (Fin.cases r9_row20
    (Fin.cases r9_row21
    (Fin.cases r9_row22
    (Fin.cases r9_row23
    (Fin.cases r9_row24
    (Fin.cases r9_row25
    (Fin.cases r9_row26
    (Fin.cases r9_row27
    (Fin.cases r9_row28
    (Fin.cases r9_row29
    (Fin.cases r9_row30
    (Fin.cases r9_row31
    (Fin.cases r9_row32
    (Fin.cases r9_row33
    (Fin.cases r9_row34
    (Fin.cases r9_row35
    (Fin.cases r9_row36
    (Fin.cases r9_row37
    (Fin.cases r9_row38
    (Fin.cases r9_row39
    (Fin.cases r9_row40
    (Fin.cases r9_row41
    (Fin.cases r9_row42
    (Fin.cases r9_row43
    (Fin.cases r9_row44
    (Fin.cases r9_row45
    (Fin.cases r9_row46
    (Fin.cases r9_row47
    (Fin.cases r9_row48
    (Fin.cases r9_row49
    (Fin.cases r9_row50
    (Fin.cases r9_row51
    (Fin.cases r9_row52
    (Fin.cases r9_row53
    (Fin.cases r9_row54
    (Fin.cases r9_row55
    (Fin.cases r9_row56
    (Fin.cases r9_row57
    (Fin.cases r9_row58
    (Fin.cases r9_row59
    (Fin.cases r9_row60
    (Fin.cases r9_row61
    (Fin.cases r9_row62
    (Fin.cases r9_row63
    (Fin.cases r9_row64
    (Fin.cases r9_row65
    (Fin.cases r9_row66
    (Fin.cases r9_row67
    (Fin.cases r9_row68
    (Fin.cases r9_row69
    (Fin.cases r9_row70
    (Fin.cases r9_row71
    (Fin.cases r9_row72
    (Fin.cases r9_row73
    (Fin.cases r9_row74
    (Fin.cases r9_row75
    (Fin.cases r9_row76
    (Fin.cases r9_row77
    (Fin.cases r9_row78
    (Fin.cases r9_row79
    (Fin.cases r9_row80
    (Fin.cases r9_row81
    (Fin.cases r9_row82
    (Fin.cases r9_row83
    (Fin.cases r9_row84
    (Fin.cases r9_row85
    (Fin.cases r9_row86
    (Fin.cases r9_row87
    (Fin.cases r9_row88
    (Fin.cases r9_row89
    (Fin.cases r9_row90
    (Fin.cases r9_row91
    (Fin.cases r9_row92
    (Fin.cases r9_row93
    (Fin.cases r9_row94
    (Fin.cases r9_row95
    (Fin.cases r9_row96
    (Fin.cases r9_row97
    (Fin.cases r9_row98
    (Fin.cases r9_row99
    (Fin.cases r9_row100
    (Fin.cases r9_row101
    (Fin.cases r9_row102
    (Fin.cases r9_row103
    (Fin.cases r9_row104
    (Fin.cases r9_row105
    (Fin.cases r9_row106
    (Fin.cases r9_row107
    (Fin.cases r9_row108
    (Fin.cases r9_row109
    (Fin.cases r9_row110
    (fun i => Fin.elim0 i))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

/-- Kernel-checked multiplication in the actual matrix algebra. -/
public theorem mul_r9 : abMatrix * r8Matrix = r9Matrix :=
  decode_mul _ _ _ ab_small r8_small r9_rows

end Lyons.SimplicityCertificate.LocalCommutant.Words
