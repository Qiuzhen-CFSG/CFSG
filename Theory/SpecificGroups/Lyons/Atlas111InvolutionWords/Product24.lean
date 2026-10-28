module

public import Theory.SpecificGroups.Lyons.Atlas111InvolutionWords.Data

/-!
# Involution word multiplication: v4 times v4

The carry-free arithmetic soundness theorem converts the 111
closed row checks into the displayed matrix identity.

Source and reproducible candidate generation:
`Atlas111InvolutionSource/GenerateWords.py` and the attributed
original matrices in `Atlas111Source/`. All checks run in Lean's kernel.
-/

namespace Lyons.Atlas111InvolutionWords

open Atlas111WordCertificate

set_option Elab.async false

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem v8_row0 :
    digitsEq 111 (rowProduct (v4Rows 0) v4Rows 111) (v8Rows 0)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem v8_row1 :
    digitsEq 111 (rowProduct (v4Rows 1) v4Rows 111) (v8Rows 1)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem v8_row2 :
    digitsEq 111 (rowProduct (v4Rows 2) v4Rows 111) (v8Rows 2)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem v8_row3 :
    digitsEq 111 (rowProduct (v4Rows 3) v4Rows 111) (v8Rows 3)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem v8_row4 :
    digitsEq 111 (rowProduct (v4Rows 4) v4Rows 111) (v8Rows 4)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem v8_row5 :
    digitsEq 111 (rowProduct (v4Rows 5) v4Rows 111) (v8Rows 5)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem v8_row6 :
    digitsEq 111 (rowProduct (v4Rows 6) v4Rows 111) (v8Rows 6)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem v8_row7 :
    digitsEq 111 (rowProduct (v4Rows 7) v4Rows 111) (v8Rows 7)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem v8_row8 :
    digitsEq 111 (rowProduct (v4Rows 8) v4Rows 111) (v8Rows 8)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem v8_row9 :
    digitsEq 111 (rowProduct (v4Rows 9) v4Rows 111) (v8Rows 9)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem v8_row10 :
    digitsEq 111 (rowProduct (v4Rows 10) v4Rows 111) (v8Rows 10)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem v8_row11 :
    digitsEq 111 (rowProduct (v4Rows 11) v4Rows 111) (v8Rows 11)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem v8_row12 :
    digitsEq 111 (rowProduct (v4Rows 12) v4Rows 111) (v8Rows 12)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem v8_row13 :
    digitsEq 111 (rowProduct (v4Rows 13) v4Rows 111) (v8Rows 13)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem v8_row14 :
    digitsEq 111 (rowProduct (v4Rows 14) v4Rows 111) (v8Rows 14)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem v8_row15 :
    digitsEq 111 (rowProduct (v4Rows 15) v4Rows 111) (v8Rows 15)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem v8_row16 :
    digitsEq 111 (rowProduct (v4Rows 16) v4Rows 111) (v8Rows 16)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem v8_row17 :
    digitsEq 111 (rowProduct (v4Rows 17) v4Rows 111) (v8Rows 17)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem v8_row18 :
    digitsEq 111 (rowProduct (v4Rows 18) v4Rows 111) (v8Rows 18)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem v8_row19 :
    digitsEq 111 (rowProduct (v4Rows 19) v4Rows 111) (v8Rows 19)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem v8_row20 :
    digitsEq 111 (rowProduct (v4Rows 20) v4Rows 111) (v8Rows 20)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem v8_row21 :
    digitsEq 111 (rowProduct (v4Rows 21) v4Rows 111) (v8Rows 21)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem v8_row22 :
    digitsEq 111 (rowProduct (v4Rows 22) v4Rows 111) (v8Rows 22)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem v8_row23 :
    digitsEq 111 (rowProduct (v4Rows 23) v4Rows 111) (v8Rows 23)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem v8_row24 :
    digitsEq 111 (rowProduct (v4Rows 24) v4Rows 111) (v8Rows 24)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem v8_row25 :
    digitsEq 111 (rowProduct (v4Rows 25) v4Rows 111) (v8Rows 25)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem v8_row26 :
    digitsEq 111 (rowProduct (v4Rows 26) v4Rows 111) (v8Rows 26)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem v8_row27 :
    digitsEq 111 (rowProduct (v4Rows 27) v4Rows 111) (v8Rows 27)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem v8_row28 :
    digitsEq 111 (rowProduct (v4Rows 28) v4Rows 111) (v8Rows 28)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem v8_row29 :
    digitsEq 111 (rowProduct (v4Rows 29) v4Rows 111) (v8Rows 29)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem v8_row30 :
    digitsEq 111 (rowProduct (v4Rows 30) v4Rows 111) (v8Rows 30)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem v8_row31 :
    digitsEq 111 (rowProduct (v4Rows 31) v4Rows 111) (v8Rows 31)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem v8_row32 :
    digitsEq 111 (rowProduct (v4Rows 32) v4Rows 111) (v8Rows 32)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem v8_row33 :
    digitsEq 111 (rowProduct (v4Rows 33) v4Rows 111) (v8Rows 33)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem v8_row34 :
    digitsEq 111 (rowProduct (v4Rows 34) v4Rows 111) (v8Rows 34)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem v8_row35 :
    digitsEq 111 (rowProduct (v4Rows 35) v4Rows 111) (v8Rows 35)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem v8_row36 :
    digitsEq 111 (rowProduct (v4Rows 36) v4Rows 111) (v8Rows 36)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem v8_row37 :
    digitsEq 111 (rowProduct (v4Rows 37) v4Rows 111) (v8Rows 37)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem v8_row38 :
    digitsEq 111 (rowProduct (v4Rows 38) v4Rows 111) (v8Rows 38)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem v8_row39 :
    digitsEq 111 (rowProduct (v4Rows 39) v4Rows 111) (v8Rows 39)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem v8_row40 :
    digitsEq 111 (rowProduct (v4Rows 40) v4Rows 111) (v8Rows 40)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem v8_row41 :
    digitsEq 111 (rowProduct (v4Rows 41) v4Rows 111) (v8Rows 41)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem v8_row42 :
    digitsEq 111 (rowProduct (v4Rows 42) v4Rows 111) (v8Rows 42)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem v8_row43 :
    digitsEq 111 (rowProduct (v4Rows 43) v4Rows 111) (v8Rows 43)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem v8_row44 :
    digitsEq 111 (rowProduct (v4Rows 44) v4Rows 111) (v8Rows 44)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem v8_row45 :
    digitsEq 111 (rowProduct (v4Rows 45) v4Rows 111) (v8Rows 45)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem v8_row46 :
    digitsEq 111 (rowProduct (v4Rows 46) v4Rows 111) (v8Rows 46)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem v8_row47 :
    digitsEq 111 (rowProduct (v4Rows 47) v4Rows 111) (v8Rows 47)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem v8_row48 :
    digitsEq 111 (rowProduct (v4Rows 48) v4Rows 111) (v8Rows 48)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem v8_row49 :
    digitsEq 111 (rowProduct (v4Rows 49) v4Rows 111) (v8Rows 49)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem v8_row50 :
    digitsEq 111 (rowProduct (v4Rows 50) v4Rows 111) (v8Rows 50)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem v8_row51 :
    digitsEq 111 (rowProduct (v4Rows 51) v4Rows 111) (v8Rows 51)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem v8_row52 :
    digitsEq 111 (rowProduct (v4Rows 52) v4Rows 111) (v8Rows 52)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem v8_row53 :
    digitsEq 111 (rowProduct (v4Rows 53) v4Rows 111) (v8Rows 53)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem v8_row54 :
    digitsEq 111 (rowProduct (v4Rows 54) v4Rows 111) (v8Rows 54)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem v8_row55 :
    digitsEq 111 (rowProduct (v4Rows 55) v4Rows 111) (v8Rows 55)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem v8_row56 :
    digitsEq 111 (rowProduct (v4Rows 56) v4Rows 111) (v8Rows 56)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem v8_row57 :
    digitsEq 111 (rowProduct (v4Rows 57) v4Rows 111) (v8Rows 57)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem v8_row58 :
    digitsEq 111 (rowProduct (v4Rows 58) v4Rows 111) (v8Rows 58)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem v8_row59 :
    digitsEq 111 (rowProduct (v4Rows 59) v4Rows 111) (v8Rows 59)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem v8_row60 :
    digitsEq 111 (rowProduct (v4Rows 60) v4Rows 111) (v8Rows 60)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem v8_row61 :
    digitsEq 111 (rowProduct (v4Rows 61) v4Rows 111) (v8Rows 61)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem v8_row62 :
    digitsEq 111 (rowProduct (v4Rows 62) v4Rows 111) (v8Rows 62)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem v8_row63 :
    digitsEq 111 (rowProduct (v4Rows 63) v4Rows 111) (v8Rows 63)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem v8_row64 :
    digitsEq 111 (rowProduct (v4Rows 64) v4Rows 111) (v8Rows 64)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem v8_row65 :
    digitsEq 111 (rowProduct (v4Rows 65) v4Rows 111) (v8Rows 65)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem v8_row66 :
    digitsEq 111 (rowProduct (v4Rows 66) v4Rows 111) (v8Rows 66)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem v8_row67 :
    digitsEq 111 (rowProduct (v4Rows 67) v4Rows 111) (v8Rows 67)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem v8_row68 :
    digitsEq 111 (rowProduct (v4Rows 68) v4Rows 111) (v8Rows 68)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem v8_row69 :
    digitsEq 111 (rowProduct (v4Rows 69) v4Rows 111) (v8Rows 69)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem v8_row70 :
    digitsEq 111 (rowProduct (v4Rows 70) v4Rows 111) (v8Rows 70)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem v8_row71 :
    digitsEq 111 (rowProduct (v4Rows 71) v4Rows 111) (v8Rows 71)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem v8_row72 :
    digitsEq 111 (rowProduct (v4Rows 72) v4Rows 111) (v8Rows 72)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem v8_row73 :
    digitsEq 111 (rowProduct (v4Rows 73) v4Rows 111) (v8Rows 73)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem v8_row74 :
    digitsEq 111 (rowProduct (v4Rows 74) v4Rows 111) (v8Rows 74)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem v8_row75 :
    digitsEq 111 (rowProduct (v4Rows 75) v4Rows 111) (v8Rows 75)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem v8_row76 :
    digitsEq 111 (rowProduct (v4Rows 76) v4Rows 111) (v8Rows 76)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem v8_row77 :
    digitsEq 111 (rowProduct (v4Rows 77) v4Rows 111) (v8Rows 77)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem v8_row78 :
    digitsEq 111 (rowProduct (v4Rows 78) v4Rows 111) (v8Rows 78)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem v8_row79 :
    digitsEq 111 (rowProduct (v4Rows 79) v4Rows 111) (v8Rows 79)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem v8_row80 :
    digitsEq 111 (rowProduct (v4Rows 80) v4Rows 111) (v8Rows 80)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem v8_row81 :
    digitsEq 111 (rowProduct (v4Rows 81) v4Rows 111) (v8Rows 81)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem v8_row82 :
    digitsEq 111 (rowProduct (v4Rows 82) v4Rows 111) (v8Rows 82)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem v8_row83 :
    digitsEq 111 (rowProduct (v4Rows 83) v4Rows 111) (v8Rows 83)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem v8_row84 :
    digitsEq 111 (rowProduct (v4Rows 84) v4Rows 111) (v8Rows 84)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem v8_row85 :
    digitsEq 111 (rowProduct (v4Rows 85) v4Rows 111) (v8Rows 85)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem v8_row86 :
    digitsEq 111 (rowProduct (v4Rows 86) v4Rows 111) (v8Rows 86)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem v8_row87 :
    digitsEq 111 (rowProduct (v4Rows 87) v4Rows 111) (v8Rows 87)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem v8_row88 :
    digitsEq 111 (rowProduct (v4Rows 88) v4Rows 111) (v8Rows 88)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem v8_row89 :
    digitsEq 111 (rowProduct (v4Rows 89) v4Rows 111) (v8Rows 89)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem v8_row90 :
    digitsEq 111 (rowProduct (v4Rows 90) v4Rows 111) (v8Rows 90)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem v8_row91 :
    digitsEq 111 (rowProduct (v4Rows 91) v4Rows 111) (v8Rows 91)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem v8_row92 :
    digitsEq 111 (rowProduct (v4Rows 92) v4Rows 111) (v8Rows 92)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem v8_row93 :
    digitsEq 111 (rowProduct (v4Rows 93) v4Rows 111) (v8Rows 93)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem v8_row94 :
    digitsEq 111 (rowProduct (v4Rows 94) v4Rows 111) (v8Rows 94)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem v8_row95 :
    digitsEq 111 (rowProduct (v4Rows 95) v4Rows 111) (v8Rows 95)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem v8_row96 :
    digitsEq 111 (rowProduct (v4Rows 96) v4Rows 111) (v8Rows 96)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem v8_row97 :
    digitsEq 111 (rowProduct (v4Rows 97) v4Rows 111) (v8Rows 97)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem v8_row98 :
    digitsEq 111 (rowProduct (v4Rows 98) v4Rows 111) (v8Rows 98)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem v8_row99 :
    digitsEq 111 (rowProduct (v4Rows 99) v4Rows 111) (v8Rows 99)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem v8_row100 :
    digitsEq 111 (rowProduct (v4Rows 100) v4Rows 111) (v8Rows 100)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem v8_row101 :
    digitsEq 111 (rowProduct (v4Rows 101) v4Rows 111) (v8Rows 101)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem v8_row102 :
    digitsEq 111 (rowProduct (v4Rows 102) v4Rows 111) (v8Rows 102)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem v8_row103 :
    digitsEq 111 (rowProduct (v4Rows 103) v4Rows 111) (v8Rows 103)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem v8_row104 :
    digitsEq 111 (rowProduct (v4Rows 104) v4Rows 111) (v8Rows 104)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem v8_row105 :
    digitsEq 111 (rowProduct (v4Rows 105) v4Rows 111) (v8Rows 105)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem v8_row106 :
    digitsEq 111 (rowProduct (v4Rows 106) v4Rows 111) (v8Rows 106)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem v8_row107 :
    digitsEq 111 (rowProduct (v4Rows 107) v4Rows 111) (v8Rows 107)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem v8_row108 :
    digitsEq 111 (rowProduct (v4Rows 108) v4Rows 111) (v8Rows 108)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem v8_row109 :
    digitsEq 111 (rowProduct (v4Rows 109) v4Rows 111) (v8Rows 109)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem v8_row110 :
    digitsEq 111 (rowProduct (v4Rows 110) v4Rows 111) (v8Rows 110)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem v8_rows : ∀ i,
    digitsEq 111 (rowProduct (v4Rows i) v4Rows 111) (v8Rows i) = true :=
  (Fin.cases v8_row0
    (Fin.cases v8_row1
    (Fin.cases v8_row2
    (Fin.cases v8_row3
    (Fin.cases v8_row4
    (Fin.cases v8_row5
    (Fin.cases v8_row6
    (Fin.cases v8_row7
    (Fin.cases v8_row8
    (Fin.cases v8_row9
    (Fin.cases v8_row10
    (Fin.cases v8_row11
    (Fin.cases v8_row12
    (Fin.cases v8_row13
    (Fin.cases v8_row14
    (Fin.cases v8_row15
    (Fin.cases v8_row16
    (Fin.cases v8_row17
    (Fin.cases v8_row18
    (Fin.cases v8_row19
    (Fin.cases v8_row20
    (Fin.cases v8_row21
    (Fin.cases v8_row22
    (Fin.cases v8_row23
    (Fin.cases v8_row24
    (Fin.cases v8_row25
    (Fin.cases v8_row26
    (Fin.cases v8_row27
    (Fin.cases v8_row28
    (Fin.cases v8_row29
    (Fin.cases v8_row30
    (Fin.cases v8_row31
    (Fin.cases v8_row32
    (Fin.cases v8_row33
    (Fin.cases v8_row34
    (Fin.cases v8_row35
    (Fin.cases v8_row36
    (Fin.cases v8_row37
    (Fin.cases v8_row38
    (Fin.cases v8_row39
    (Fin.cases v8_row40
    (Fin.cases v8_row41
    (Fin.cases v8_row42
    (Fin.cases v8_row43
    (Fin.cases v8_row44
    (Fin.cases v8_row45
    (Fin.cases v8_row46
    (Fin.cases v8_row47
    (Fin.cases v8_row48
    (Fin.cases v8_row49
    (Fin.cases v8_row50
    (Fin.cases v8_row51
    (Fin.cases v8_row52
    (Fin.cases v8_row53
    (Fin.cases v8_row54
    (Fin.cases v8_row55
    (Fin.cases v8_row56
    (Fin.cases v8_row57
    (Fin.cases v8_row58
    (Fin.cases v8_row59
    (Fin.cases v8_row60
    (Fin.cases v8_row61
    (Fin.cases v8_row62
    (Fin.cases v8_row63
    (Fin.cases v8_row64
    (Fin.cases v8_row65
    (Fin.cases v8_row66
    (Fin.cases v8_row67
    (Fin.cases v8_row68
    (Fin.cases v8_row69
    (Fin.cases v8_row70
    (Fin.cases v8_row71
    (Fin.cases v8_row72
    (Fin.cases v8_row73
    (Fin.cases v8_row74
    (Fin.cases v8_row75
    (Fin.cases v8_row76
    (Fin.cases v8_row77
    (Fin.cases v8_row78
    (Fin.cases v8_row79
    (Fin.cases v8_row80
    (Fin.cases v8_row81
    (Fin.cases v8_row82
    (Fin.cases v8_row83
    (Fin.cases v8_row84
    (Fin.cases v8_row85
    (Fin.cases v8_row86
    (Fin.cases v8_row87
    (Fin.cases v8_row88
    (Fin.cases v8_row89
    (Fin.cases v8_row90
    (Fin.cases v8_row91
    (Fin.cases v8_row92
    (Fin.cases v8_row93
    (Fin.cases v8_row94
    (Fin.cases v8_row95
    (Fin.cases v8_row96
    (Fin.cases v8_row97
    (Fin.cases v8_row98
    (Fin.cases v8_row99
    (Fin.cases v8_row100
    (Fin.cases v8_row101
    (Fin.cases v8_row102
    (Fin.cases v8_row103
    (Fin.cases v8_row104
    (Fin.cases v8_row105
    (Fin.cases v8_row106
    (Fin.cases v8_row107
    (Fin.cases v8_row108
    (Fin.cases v8_row109
    (Fin.cases v8_row110
    (fun i => Fin.elim0 i))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

/-- Kernel-checked multiplication in the actual matrix algebra. -/
public theorem mul_v8 : v4Matrix * v4Matrix = v8Matrix :=
  decode_mul _ _ _ v4_small v4_small v8_rows

end Lyons.Atlas111InvolutionWords
