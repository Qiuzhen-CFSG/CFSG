module

public import Theory.SpecificGroups.Lyons.Atlas111InvolutionWords.Data

/-!
# Involution word multiplication: v9 times v9

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
private theorem v18_row0 :
    digitsEq 111 (rowProduct (v9Rows 0) v9Rows 111) (v18Rows 0)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem v18_row1 :
    digitsEq 111 (rowProduct (v9Rows 1) v9Rows 111) (v18Rows 1)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem v18_row2 :
    digitsEq 111 (rowProduct (v9Rows 2) v9Rows 111) (v18Rows 2)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem v18_row3 :
    digitsEq 111 (rowProduct (v9Rows 3) v9Rows 111) (v18Rows 3)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem v18_row4 :
    digitsEq 111 (rowProduct (v9Rows 4) v9Rows 111) (v18Rows 4)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem v18_row5 :
    digitsEq 111 (rowProduct (v9Rows 5) v9Rows 111) (v18Rows 5)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem v18_row6 :
    digitsEq 111 (rowProduct (v9Rows 6) v9Rows 111) (v18Rows 6)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem v18_row7 :
    digitsEq 111 (rowProduct (v9Rows 7) v9Rows 111) (v18Rows 7)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem v18_row8 :
    digitsEq 111 (rowProduct (v9Rows 8) v9Rows 111) (v18Rows 8)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem v18_row9 :
    digitsEq 111 (rowProduct (v9Rows 9) v9Rows 111) (v18Rows 9)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem v18_row10 :
    digitsEq 111 (rowProduct (v9Rows 10) v9Rows 111) (v18Rows 10)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem v18_row11 :
    digitsEq 111 (rowProduct (v9Rows 11) v9Rows 111) (v18Rows 11)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem v18_row12 :
    digitsEq 111 (rowProduct (v9Rows 12) v9Rows 111) (v18Rows 12)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem v18_row13 :
    digitsEq 111 (rowProduct (v9Rows 13) v9Rows 111) (v18Rows 13)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem v18_row14 :
    digitsEq 111 (rowProduct (v9Rows 14) v9Rows 111) (v18Rows 14)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem v18_row15 :
    digitsEq 111 (rowProduct (v9Rows 15) v9Rows 111) (v18Rows 15)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem v18_row16 :
    digitsEq 111 (rowProduct (v9Rows 16) v9Rows 111) (v18Rows 16)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem v18_row17 :
    digitsEq 111 (rowProduct (v9Rows 17) v9Rows 111) (v18Rows 17)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem v18_row18 :
    digitsEq 111 (rowProduct (v9Rows 18) v9Rows 111) (v18Rows 18)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem v18_row19 :
    digitsEq 111 (rowProduct (v9Rows 19) v9Rows 111) (v18Rows 19)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem v18_row20 :
    digitsEq 111 (rowProduct (v9Rows 20) v9Rows 111) (v18Rows 20)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem v18_row21 :
    digitsEq 111 (rowProduct (v9Rows 21) v9Rows 111) (v18Rows 21)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem v18_row22 :
    digitsEq 111 (rowProduct (v9Rows 22) v9Rows 111) (v18Rows 22)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem v18_row23 :
    digitsEq 111 (rowProduct (v9Rows 23) v9Rows 111) (v18Rows 23)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem v18_row24 :
    digitsEq 111 (rowProduct (v9Rows 24) v9Rows 111) (v18Rows 24)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem v18_row25 :
    digitsEq 111 (rowProduct (v9Rows 25) v9Rows 111) (v18Rows 25)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem v18_row26 :
    digitsEq 111 (rowProduct (v9Rows 26) v9Rows 111) (v18Rows 26)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem v18_row27 :
    digitsEq 111 (rowProduct (v9Rows 27) v9Rows 111) (v18Rows 27)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem v18_row28 :
    digitsEq 111 (rowProduct (v9Rows 28) v9Rows 111) (v18Rows 28)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem v18_row29 :
    digitsEq 111 (rowProduct (v9Rows 29) v9Rows 111) (v18Rows 29)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem v18_row30 :
    digitsEq 111 (rowProduct (v9Rows 30) v9Rows 111) (v18Rows 30)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem v18_row31 :
    digitsEq 111 (rowProduct (v9Rows 31) v9Rows 111) (v18Rows 31)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem v18_row32 :
    digitsEq 111 (rowProduct (v9Rows 32) v9Rows 111) (v18Rows 32)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem v18_row33 :
    digitsEq 111 (rowProduct (v9Rows 33) v9Rows 111) (v18Rows 33)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem v18_row34 :
    digitsEq 111 (rowProduct (v9Rows 34) v9Rows 111) (v18Rows 34)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem v18_row35 :
    digitsEq 111 (rowProduct (v9Rows 35) v9Rows 111) (v18Rows 35)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem v18_row36 :
    digitsEq 111 (rowProduct (v9Rows 36) v9Rows 111) (v18Rows 36)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem v18_row37 :
    digitsEq 111 (rowProduct (v9Rows 37) v9Rows 111) (v18Rows 37)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem v18_row38 :
    digitsEq 111 (rowProduct (v9Rows 38) v9Rows 111) (v18Rows 38)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem v18_row39 :
    digitsEq 111 (rowProduct (v9Rows 39) v9Rows 111) (v18Rows 39)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem v18_row40 :
    digitsEq 111 (rowProduct (v9Rows 40) v9Rows 111) (v18Rows 40)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem v18_row41 :
    digitsEq 111 (rowProduct (v9Rows 41) v9Rows 111) (v18Rows 41)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem v18_row42 :
    digitsEq 111 (rowProduct (v9Rows 42) v9Rows 111) (v18Rows 42)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem v18_row43 :
    digitsEq 111 (rowProduct (v9Rows 43) v9Rows 111) (v18Rows 43)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem v18_row44 :
    digitsEq 111 (rowProduct (v9Rows 44) v9Rows 111) (v18Rows 44)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem v18_row45 :
    digitsEq 111 (rowProduct (v9Rows 45) v9Rows 111) (v18Rows 45)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem v18_row46 :
    digitsEq 111 (rowProduct (v9Rows 46) v9Rows 111) (v18Rows 46)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem v18_row47 :
    digitsEq 111 (rowProduct (v9Rows 47) v9Rows 111) (v18Rows 47)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem v18_row48 :
    digitsEq 111 (rowProduct (v9Rows 48) v9Rows 111) (v18Rows 48)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem v18_row49 :
    digitsEq 111 (rowProduct (v9Rows 49) v9Rows 111) (v18Rows 49)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem v18_row50 :
    digitsEq 111 (rowProduct (v9Rows 50) v9Rows 111) (v18Rows 50)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem v18_row51 :
    digitsEq 111 (rowProduct (v9Rows 51) v9Rows 111) (v18Rows 51)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem v18_row52 :
    digitsEq 111 (rowProduct (v9Rows 52) v9Rows 111) (v18Rows 52)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem v18_row53 :
    digitsEq 111 (rowProduct (v9Rows 53) v9Rows 111) (v18Rows 53)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem v18_row54 :
    digitsEq 111 (rowProduct (v9Rows 54) v9Rows 111) (v18Rows 54)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem v18_row55 :
    digitsEq 111 (rowProduct (v9Rows 55) v9Rows 111) (v18Rows 55)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem v18_row56 :
    digitsEq 111 (rowProduct (v9Rows 56) v9Rows 111) (v18Rows 56)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem v18_row57 :
    digitsEq 111 (rowProduct (v9Rows 57) v9Rows 111) (v18Rows 57)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem v18_row58 :
    digitsEq 111 (rowProduct (v9Rows 58) v9Rows 111) (v18Rows 58)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem v18_row59 :
    digitsEq 111 (rowProduct (v9Rows 59) v9Rows 111) (v18Rows 59)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem v18_row60 :
    digitsEq 111 (rowProduct (v9Rows 60) v9Rows 111) (v18Rows 60)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem v18_row61 :
    digitsEq 111 (rowProduct (v9Rows 61) v9Rows 111) (v18Rows 61)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem v18_row62 :
    digitsEq 111 (rowProduct (v9Rows 62) v9Rows 111) (v18Rows 62)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem v18_row63 :
    digitsEq 111 (rowProduct (v9Rows 63) v9Rows 111) (v18Rows 63)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem v18_row64 :
    digitsEq 111 (rowProduct (v9Rows 64) v9Rows 111) (v18Rows 64)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem v18_row65 :
    digitsEq 111 (rowProduct (v9Rows 65) v9Rows 111) (v18Rows 65)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem v18_row66 :
    digitsEq 111 (rowProduct (v9Rows 66) v9Rows 111) (v18Rows 66)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem v18_row67 :
    digitsEq 111 (rowProduct (v9Rows 67) v9Rows 111) (v18Rows 67)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem v18_row68 :
    digitsEq 111 (rowProduct (v9Rows 68) v9Rows 111) (v18Rows 68)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem v18_row69 :
    digitsEq 111 (rowProduct (v9Rows 69) v9Rows 111) (v18Rows 69)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem v18_row70 :
    digitsEq 111 (rowProduct (v9Rows 70) v9Rows 111) (v18Rows 70)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem v18_row71 :
    digitsEq 111 (rowProduct (v9Rows 71) v9Rows 111) (v18Rows 71)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem v18_row72 :
    digitsEq 111 (rowProduct (v9Rows 72) v9Rows 111) (v18Rows 72)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem v18_row73 :
    digitsEq 111 (rowProduct (v9Rows 73) v9Rows 111) (v18Rows 73)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem v18_row74 :
    digitsEq 111 (rowProduct (v9Rows 74) v9Rows 111) (v18Rows 74)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem v18_row75 :
    digitsEq 111 (rowProduct (v9Rows 75) v9Rows 111) (v18Rows 75)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem v18_row76 :
    digitsEq 111 (rowProduct (v9Rows 76) v9Rows 111) (v18Rows 76)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem v18_row77 :
    digitsEq 111 (rowProduct (v9Rows 77) v9Rows 111) (v18Rows 77)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem v18_row78 :
    digitsEq 111 (rowProduct (v9Rows 78) v9Rows 111) (v18Rows 78)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem v18_row79 :
    digitsEq 111 (rowProduct (v9Rows 79) v9Rows 111) (v18Rows 79)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem v18_row80 :
    digitsEq 111 (rowProduct (v9Rows 80) v9Rows 111) (v18Rows 80)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem v18_row81 :
    digitsEq 111 (rowProduct (v9Rows 81) v9Rows 111) (v18Rows 81)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem v18_row82 :
    digitsEq 111 (rowProduct (v9Rows 82) v9Rows 111) (v18Rows 82)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem v18_row83 :
    digitsEq 111 (rowProduct (v9Rows 83) v9Rows 111) (v18Rows 83)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem v18_row84 :
    digitsEq 111 (rowProduct (v9Rows 84) v9Rows 111) (v18Rows 84)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem v18_row85 :
    digitsEq 111 (rowProduct (v9Rows 85) v9Rows 111) (v18Rows 85)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem v18_row86 :
    digitsEq 111 (rowProduct (v9Rows 86) v9Rows 111) (v18Rows 86)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem v18_row87 :
    digitsEq 111 (rowProduct (v9Rows 87) v9Rows 111) (v18Rows 87)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem v18_row88 :
    digitsEq 111 (rowProduct (v9Rows 88) v9Rows 111) (v18Rows 88)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem v18_row89 :
    digitsEq 111 (rowProduct (v9Rows 89) v9Rows 111) (v18Rows 89)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem v18_row90 :
    digitsEq 111 (rowProduct (v9Rows 90) v9Rows 111) (v18Rows 90)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem v18_row91 :
    digitsEq 111 (rowProduct (v9Rows 91) v9Rows 111) (v18Rows 91)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem v18_row92 :
    digitsEq 111 (rowProduct (v9Rows 92) v9Rows 111) (v18Rows 92)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem v18_row93 :
    digitsEq 111 (rowProduct (v9Rows 93) v9Rows 111) (v18Rows 93)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem v18_row94 :
    digitsEq 111 (rowProduct (v9Rows 94) v9Rows 111) (v18Rows 94)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem v18_row95 :
    digitsEq 111 (rowProduct (v9Rows 95) v9Rows 111) (v18Rows 95)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem v18_row96 :
    digitsEq 111 (rowProduct (v9Rows 96) v9Rows 111) (v18Rows 96)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem v18_row97 :
    digitsEq 111 (rowProduct (v9Rows 97) v9Rows 111) (v18Rows 97)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem v18_row98 :
    digitsEq 111 (rowProduct (v9Rows 98) v9Rows 111) (v18Rows 98)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem v18_row99 :
    digitsEq 111 (rowProduct (v9Rows 99) v9Rows 111) (v18Rows 99)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem v18_row100 :
    digitsEq 111 (rowProduct (v9Rows 100) v9Rows 111) (v18Rows 100)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem v18_row101 :
    digitsEq 111 (rowProduct (v9Rows 101) v9Rows 111) (v18Rows 101)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem v18_row102 :
    digitsEq 111 (rowProduct (v9Rows 102) v9Rows 111) (v18Rows 102)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem v18_row103 :
    digitsEq 111 (rowProduct (v9Rows 103) v9Rows 111) (v18Rows 103)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem v18_row104 :
    digitsEq 111 (rowProduct (v9Rows 104) v9Rows 111) (v18Rows 104)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem v18_row105 :
    digitsEq 111 (rowProduct (v9Rows 105) v9Rows 111) (v18Rows 105)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem v18_row106 :
    digitsEq 111 (rowProduct (v9Rows 106) v9Rows 111) (v18Rows 106)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem v18_row107 :
    digitsEq 111 (rowProduct (v9Rows 107) v9Rows 111) (v18Rows 107)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem v18_row108 :
    digitsEq 111 (rowProduct (v9Rows 108) v9Rows 111) (v18Rows 108)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem v18_row109 :
    digitsEq 111 (rowProduct (v9Rows 109) v9Rows 111) (v18Rows 109)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem v18_row110 :
    digitsEq 111 (rowProduct (v9Rows 110) v9Rows 111) (v18Rows 110)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem v18_rows : ∀ i,
    digitsEq 111 (rowProduct (v9Rows i) v9Rows 111) (v18Rows i) = true :=
  (Fin.cases v18_row0
    (Fin.cases v18_row1
    (Fin.cases v18_row2
    (Fin.cases v18_row3
    (Fin.cases v18_row4
    (Fin.cases v18_row5
    (Fin.cases v18_row6
    (Fin.cases v18_row7
    (Fin.cases v18_row8
    (Fin.cases v18_row9
    (Fin.cases v18_row10
    (Fin.cases v18_row11
    (Fin.cases v18_row12
    (Fin.cases v18_row13
    (Fin.cases v18_row14
    (Fin.cases v18_row15
    (Fin.cases v18_row16
    (Fin.cases v18_row17
    (Fin.cases v18_row18
    (Fin.cases v18_row19
    (Fin.cases v18_row20
    (Fin.cases v18_row21
    (Fin.cases v18_row22
    (Fin.cases v18_row23
    (Fin.cases v18_row24
    (Fin.cases v18_row25
    (Fin.cases v18_row26
    (Fin.cases v18_row27
    (Fin.cases v18_row28
    (Fin.cases v18_row29
    (Fin.cases v18_row30
    (Fin.cases v18_row31
    (Fin.cases v18_row32
    (Fin.cases v18_row33
    (Fin.cases v18_row34
    (Fin.cases v18_row35
    (Fin.cases v18_row36
    (Fin.cases v18_row37
    (Fin.cases v18_row38
    (Fin.cases v18_row39
    (Fin.cases v18_row40
    (Fin.cases v18_row41
    (Fin.cases v18_row42
    (Fin.cases v18_row43
    (Fin.cases v18_row44
    (Fin.cases v18_row45
    (Fin.cases v18_row46
    (Fin.cases v18_row47
    (Fin.cases v18_row48
    (Fin.cases v18_row49
    (Fin.cases v18_row50
    (Fin.cases v18_row51
    (Fin.cases v18_row52
    (Fin.cases v18_row53
    (Fin.cases v18_row54
    (Fin.cases v18_row55
    (Fin.cases v18_row56
    (Fin.cases v18_row57
    (Fin.cases v18_row58
    (Fin.cases v18_row59
    (Fin.cases v18_row60
    (Fin.cases v18_row61
    (Fin.cases v18_row62
    (Fin.cases v18_row63
    (Fin.cases v18_row64
    (Fin.cases v18_row65
    (Fin.cases v18_row66
    (Fin.cases v18_row67
    (Fin.cases v18_row68
    (Fin.cases v18_row69
    (Fin.cases v18_row70
    (Fin.cases v18_row71
    (Fin.cases v18_row72
    (Fin.cases v18_row73
    (Fin.cases v18_row74
    (Fin.cases v18_row75
    (Fin.cases v18_row76
    (Fin.cases v18_row77
    (Fin.cases v18_row78
    (Fin.cases v18_row79
    (Fin.cases v18_row80
    (Fin.cases v18_row81
    (Fin.cases v18_row82
    (Fin.cases v18_row83
    (Fin.cases v18_row84
    (Fin.cases v18_row85
    (Fin.cases v18_row86
    (Fin.cases v18_row87
    (Fin.cases v18_row88
    (Fin.cases v18_row89
    (Fin.cases v18_row90
    (Fin.cases v18_row91
    (Fin.cases v18_row92
    (Fin.cases v18_row93
    (Fin.cases v18_row94
    (Fin.cases v18_row95
    (Fin.cases v18_row96
    (Fin.cases v18_row97
    (Fin.cases v18_row98
    (Fin.cases v18_row99
    (Fin.cases v18_row100
    (Fin.cases v18_row101
    (Fin.cases v18_row102
    (Fin.cases v18_row103
    (Fin.cases v18_row104
    (Fin.cases v18_row105
    (Fin.cases v18_row106
    (Fin.cases v18_row107
    (Fin.cases v18_row108
    (Fin.cases v18_row109
    (Fin.cases v18_row110
    (fun i => Fin.elim0 i))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

/-- Kernel-checked multiplication in the actual matrix algebra. -/
public theorem mul_v18 : v9Matrix * v9Matrix = v18Matrix :=
  decode_mul _ _ _ v9_small v9_small v18_rows

end Lyons.Atlas111InvolutionWords
