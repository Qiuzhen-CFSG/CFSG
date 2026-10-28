module

public import Theory.SpecificGroups.Lyons.Atlas111InvolutionWords.Data

/-!
# Involution word multiplication: v8 times v

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
private theorem v9_row0 :
    digitsEq 111 (rowProduct (v8Rows 0) vRows 111) (v9Rows 0)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem v9_row1 :
    digitsEq 111 (rowProduct (v8Rows 1) vRows 111) (v9Rows 1)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem v9_row2 :
    digitsEq 111 (rowProduct (v8Rows 2) vRows 111) (v9Rows 2)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem v9_row3 :
    digitsEq 111 (rowProduct (v8Rows 3) vRows 111) (v9Rows 3)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem v9_row4 :
    digitsEq 111 (rowProduct (v8Rows 4) vRows 111) (v9Rows 4)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem v9_row5 :
    digitsEq 111 (rowProduct (v8Rows 5) vRows 111) (v9Rows 5)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem v9_row6 :
    digitsEq 111 (rowProduct (v8Rows 6) vRows 111) (v9Rows 6)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem v9_row7 :
    digitsEq 111 (rowProduct (v8Rows 7) vRows 111) (v9Rows 7)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem v9_row8 :
    digitsEq 111 (rowProduct (v8Rows 8) vRows 111) (v9Rows 8)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem v9_row9 :
    digitsEq 111 (rowProduct (v8Rows 9) vRows 111) (v9Rows 9)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem v9_row10 :
    digitsEq 111 (rowProduct (v8Rows 10) vRows 111) (v9Rows 10)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem v9_row11 :
    digitsEq 111 (rowProduct (v8Rows 11) vRows 111) (v9Rows 11)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem v9_row12 :
    digitsEq 111 (rowProduct (v8Rows 12) vRows 111) (v9Rows 12)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem v9_row13 :
    digitsEq 111 (rowProduct (v8Rows 13) vRows 111) (v9Rows 13)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem v9_row14 :
    digitsEq 111 (rowProduct (v8Rows 14) vRows 111) (v9Rows 14)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem v9_row15 :
    digitsEq 111 (rowProduct (v8Rows 15) vRows 111) (v9Rows 15)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem v9_row16 :
    digitsEq 111 (rowProduct (v8Rows 16) vRows 111) (v9Rows 16)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem v9_row17 :
    digitsEq 111 (rowProduct (v8Rows 17) vRows 111) (v9Rows 17)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem v9_row18 :
    digitsEq 111 (rowProduct (v8Rows 18) vRows 111) (v9Rows 18)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem v9_row19 :
    digitsEq 111 (rowProduct (v8Rows 19) vRows 111) (v9Rows 19)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem v9_row20 :
    digitsEq 111 (rowProduct (v8Rows 20) vRows 111) (v9Rows 20)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem v9_row21 :
    digitsEq 111 (rowProduct (v8Rows 21) vRows 111) (v9Rows 21)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem v9_row22 :
    digitsEq 111 (rowProduct (v8Rows 22) vRows 111) (v9Rows 22)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem v9_row23 :
    digitsEq 111 (rowProduct (v8Rows 23) vRows 111) (v9Rows 23)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem v9_row24 :
    digitsEq 111 (rowProduct (v8Rows 24) vRows 111) (v9Rows 24)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem v9_row25 :
    digitsEq 111 (rowProduct (v8Rows 25) vRows 111) (v9Rows 25)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem v9_row26 :
    digitsEq 111 (rowProduct (v8Rows 26) vRows 111) (v9Rows 26)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem v9_row27 :
    digitsEq 111 (rowProduct (v8Rows 27) vRows 111) (v9Rows 27)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem v9_row28 :
    digitsEq 111 (rowProduct (v8Rows 28) vRows 111) (v9Rows 28)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem v9_row29 :
    digitsEq 111 (rowProduct (v8Rows 29) vRows 111) (v9Rows 29)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem v9_row30 :
    digitsEq 111 (rowProduct (v8Rows 30) vRows 111) (v9Rows 30)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem v9_row31 :
    digitsEq 111 (rowProduct (v8Rows 31) vRows 111) (v9Rows 31)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem v9_row32 :
    digitsEq 111 (rowProduct (v8Rows 32) vRows 111) (v9Rows 32)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem v9_row33 :
    digitsEq 111 (rowProduct (v8Rows 33) vRows 111) (v9Rows 33)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem v9_row34 :
    digitsEq 111 (rowProduct (v8Rows 34) vRows 111) (v9Rows 34)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem v9_row35 :
    digitsEq 111 (rowProduct (v8Rows 35) vRows 111) (v9Rows 35)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem v9_row36 :
    digitsEq 111 (rowProduct (v8Rows 36) vRows 111) (v9Rows 36)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem v9_row37 :
    digitsEq 111 (rowProduct (v8Rows 37) vRows 111) (v9Rows 37)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem v9_row38 :
    digitsEq 111 (rowProduct (v8Rows 38) vRows 111) (v9Rows 38)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem v9_row39 :
    digitsEq 111 (rowProduct (v8Rows 39) vRows 111) (v9Rows 39)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem v9_row40 :
    digitsEq 111 (rowProduct (v8Rows 40) vRows 111) (v9Rows 40)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem v9_row41 :
    digitsEq 111 (rowProduct (v8Rows 41) vRows 111) (v9Rows 41)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem v9_row42 :
    digitsEq 111 (rowProduct (v8Rows 42) vRows 111) (v9Rows 42)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem v9_row43 :
    digitsEq 111 (rowProduct (v8Rows 43) vRows 111) (v9Rows 43)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem v9_row44 :
    digitsEq 111 (rowProduct (v8Rows 44) vRows 111) (v9Rows 44)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem v9_row45 :
    digitsEq 111 (rowProduct (v8Rows 45) vRows 111) (v9Rows 45)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem v9_row46 :
    digitsEq 111 (rowProduct (v8Rows 46) vRows 111) (v9Rows 46)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem v9_row47 :
    digitsEq 111 (rowProduct (v8Rows 47) vRows 111) (v9Rows 47)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem v9_row48 :
    digitsEq 111 (rowProduct (v8Rows 48) vRows 111) (v9Rows 48)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem v9_row49 :
    digitsEq 111 (rowProduct (v8Rows 49) vRows 111) (v9Rows 49)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem v9_row50 :
    digitsEq 111 (rowProduct (v8Rows 50) vRows 111) (v9Rows 50)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem v9_row51 :
    digitsEq 111 (rowProduct (v8Rows 51) vRows 111) (v9Rows 51)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem v9_row52 :
    digitsEq 111 (rowProduct (v8Rows 52) vRows 111) (v9Rows 52)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem v9_row53 :
    digitsEq 111 (rowProduct (v8Rows 53) vRows 111) (v9Rows 53)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem v9_row54 :
    digitsEq 111 (rowProduct (v8Rows 54) vRows 111) (v9Rows 54)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem v9_row55 :
    digitsEq 111 (rowProduct (v8Rows 55) vRows 111) (v9Rows 55)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem v9_row56 :
    digitsEq 111 (rowProduct (v8Rows 56) vRows 111) (v9Rows 56)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem v9_row57 :
    digitsEq 111 (rowProduct (v8Rows 57) vRows 111) (v9Rows 57)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem v9_row58 :
    digitsEq 111 (rowProduct (v8Rows 58) vRows 111) (v9Rows 58)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem v9_row59 :
    digitsEq 111 (rowProduct (v8Rows 59) vRows 111) (v9Rows 59)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem v9_row60 :
    digitsEq 111 (rowProduct (v8Rows 60) vRows 111) (v9Rows 60)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem v9_row61 :
    digitsEq 111 (rowProduct (v8Rows 61) vRows 111) (v9Rows 61)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem v9_row62 :
    digitsEq 111 (rowProduct (v8Rows 62) vRows 111) (v9Rows 62)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem v9_row63 :
    digitsEq 111 (rowProduct (v8Rows 63) vRows 111) (v9Rows 63)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem v9_row64 :
    digitsEq 111 (rowProduct (v8Rows 64) vRows 111) (v9Rows 64)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem v9_row65 :
    digitsEq 111 (rowProduct (v8Rows 65) vRows 111) (v9Rows 65)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem v9_row66 :
    digitsEq 111 (rowProduct (v8Rows 66) vRows 111) (v9Rows 66)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem v9_row67 :
    digitsEq 111 (rowProduct (v8Rows 67) vRows 111) (v9Rows 67)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem v9_row68 :
    digitsEq 111 (rowProduct (v8Rows 68) vRows 111) (v9Rows 68)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem v9_row69 :
    digitsEq 111 (rowProduct (v8Rows 69) vRows 111) (v9Rows 69)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem v9_row70 :
    digitsEq 111 (rowProduct (v8Rows 70) vRows 111) (v9Rows 70)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem v9_row71 :
    digitsEq 111 (rowProduct (v8Rows 71) vRows 111) (v9Rows 71)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem v9_row72 :
    digitsEq 111 (rowProduct (v8Rows 72) vRows 111) (v9Rows 72)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem v9_row73 :
    digitsEq 111 (rowProduct (v8Rows 73) vRows 111) (v9Rows 73)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem v9_row74 :
    digitsEq 111 (rowProduct (v8Rows 74) vRows 111) (v9Rows 74)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem v9_row75 :
    digitsEq 111 (rowProduct (v8Rows 75) vRows 111) (v9Rows 75)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem v9_row76 :
    digitsEq 111 (rowProduct (v8Rows 76) vRows 111) (v9Rows 76)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem v9_row77 :
    digitsEq 111 (rowProduct (v8Rows 77) vRows 111) (v9Rows 77)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem v9_row78 :
    digitsEq 111 (rowProduct (v8Rows 78) vRows 111) (v9Rows 78)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem v9_row79 :
    digitsEq 111 (rowProduct (v8Rows 79) vRows 111) (v9Rows 79)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem v9_row80 :
    digitsEq 111 (rowProduct (v8Rows 80) vRows 111) (v9Rows 80)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem v9_row81 :
    digitsEq 111 (rowProduct (v8Rows 81) vRows 111) (v9Rows 81)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem v9_row82 :
    digitsEq 111 (rowProduct (v8Rows 82) vRows 111) (v9Rows 82)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem v9_row83 :
    digitsEq 111 (rowProduct (v8Rows 83) vRows 111) (v9Rows 83)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem v9_row84 :
    digitsEq 111 (rowProduct (v8Rows 84) vRows 111) (v9Rows 84)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem v9_row85 :
    digitsEq 111 (rowProduct (v8Rows 85) vRows 111) (v9Rows 85)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem v9_row86 :
    digitsEq 111 (rowProduct (v8Rows 86) vRows 111) (v9Rows 86)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem v9_row87 :
    digitsEq 111 (rowProduct (v8Rows 87) vRows 111) (v9Rows 87)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem v9_row88 :
    digitsEq 111 (rowProduct (v8Rows 88) vRows 111) (v9Rows 88)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem v9_row89 :
    digitsEq 111 (rowProduct (v8Rows 89) vRows 111) (v9Rows 89)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem v9_row90 :
    digitsEq 111 (rowProduct (v8Rows 90) vRows 111) (v9Rows 90)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem v9_row91 :
    digitsEq 111 (rowProduct (v8Rows 91) vRows 111) (v9Rows 91)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem v9_row92 :
    digitsEq 111 (rowProduct (v8Rows 92) vRows 111) (v9Rows 92)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem v9_row93 :
    digitsEq 111 (rowProduct (v8Rows 93) vRows 111) (v9Rows 93)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem v9_row94 :
    digitsEq 111 (rowProduct (v8Rows 94) vRows 111) (v9Rows 94)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem v9_row95 :
    digitsEq 111 (rowProduct (v8Rows 95) vRows 111) (v9Rows 95)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem v9_row96 :
    digitsEq 111 (rowProduct (v8Rows 96) vRows 111) (v9Rows 96)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem v9_row97 :
    digitsEq 111 (rowProduct (v8Rows 97) vRows 111) (v9Rows 97)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem v9_row98 :
    digitsEq 111 (rowProduct (v8Rows 98) vRows 111) (v9Rows 98)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem v9_row99 :
    digitsEq 111 (rowProduct (v8Rows 99) vRows 111) (v9Rows 99)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem v9_row100 :
    digitsEq 111 (rowProduct (v8Rows 100) vRows 111) (v9Rows 100)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem v9_row101 :
    digitsEq 111 (rowProduct (v8Rows 101) vRows 111) (v9Rows 101)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem v9_row102 :
    digitsEq 111 (rowProduct (v8Rows 102) vRows 111) (v9Rows 102)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem v9_row103 :
    digitsEq 111 (rowProduct (v8Rows 103) vRows 111) (v9Rows 103)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem v9_row104 :
    digitsEq 111 (rowProduct (v8Rows 104) vRows 111) (v9Rows 104)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem v9_row105 :
    digitsEq 111 (rowProduct (v8Rows 105) vRows 111) (v9Rows 105)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem v9_row106 :
    digitsEq 111 (rowProduct (v8Rows 106) vRows 111) (v9Rows 106)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem v9_row107 :
    digitsEq 111 (rowProduct (v8Rows 107) vRows 111) (v9Rows 107)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem v9_row108 :
    digitsEq 111 (rowProduct (v8Rows 108) vRows 111) (v9Rows 108)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem v9_row109 :
    digitsEq 111 (rowProduct (v8Rows 109) vRows 111) (v9Rows 109)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem v9_row110 :
    digitsEq 111 (rowProduct (v8Rows 110) vRows 111) (v9Rows 110)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem v9_rows : ∀ i,
    digitsEq 111 (rowProduct (v8Rows i) vRows 111) (v9Rows i) = true :=
  (Fin.cases v9_row0
    (Fin.cases v9_row1
    (Fin.cases v9_row2
    (Fin.cases v9_row3
    (Fin.cases v9_row4
    (Fin.cases v9_row5
    (Fin.cases v9_row6
    (Fin.cases v9_row7
    (Fin.cases v9_row8
    (Fin.cases v9_row9
    (Fin.cases v9_row10
    (Fin.cases v9_row11
    (Fin.cases v9_row12
    (Fin.cases v9_row13
    (Fin.cases v9_row14
    (Fin.cases v9_row15
    (Fin.cases v9_row16
    (Fin.cases v9_row17
    (Fin.cases v9_row18
    (Fin.cases v9_row19
    (Fin.cases v9_row20
    (Fin.cases v9_row21
    (Fin.cases v9_row22
    (Fin.cases v9_row23
    (Fin.cases v9_row24
    (Fin.cases v9_row25
    (Fin.cases v9_row26
    (Fin.cases v9_row27
    (Fin.cases v9_row28
    (Fin.cases v9_row29
    (Fin.cases v9_row30
    (Fin.cases v9_row31
    (Fin.cases v9_row32
    (Fin.cases v9_row33
    (Fin.cases v9_row34
    (Fin.cases v9_row35
    (Fin.cases v9_row36
    (Fin.cases v9_row37
    (Fin.cases v9_row38
    (Fin.cases v9_row39
    (Fin.cases v9_row40
    (Fin.cases v9_row41
    (Fin.cases v9_row42
    (Fin.cases v9_row43
    (Fin.cases v9_row44
    (Fin.cases v9_row45
    (Fin.cases v9_row46
    (Fin.cases v9_row47
    (Fin.cases v9_row48
    (Fin.cases v9_row49
    (Fin.cases v9_row50
    (Fin.cases v9_row51
    (Fin.cases v9_row52
    (Fin.cases v9_row53
    (Fin.cases v9_row54
    (Fin.cases v9_row55
    (Fin.cases v9_row56
    (Fin.cases v9_row57
    (Fin.cases v9_row58
    (Fin.cases v9_row59
    (Fin.cases v9_row60
    (Fin.cases v9_row61
    (Fin.cases v9_row62
    (Fin.cases v9_row63
    (Fin.cases v9_row64
    (Fin.cases v9_row65
    (Fin.cases v9_row66
    (Fin.cases v9_row67
    (Fin.cases v9_row68
    (Fin.cases v9_row69
    (Fin.cases v9_row70
    (Fin.cases v9_row71
    (Fin.cases v9_row72
    (Fin.cases v9_row73
    (Fin.cases v9_row74
    (Fin.cases v9_row75
    (Fin.cases v9_row76
    (Fin.cases v9_row77
    (Fin.cases v9_row78
    (Fin.cases v9_row79
    (Fin.cases v9_row80
    (Fin.cases v9_row81
    (Fin.cases v9_row82
    (Fin.cases v9_row83
    (Fin.cases v9_row84
    (Fin.cases v9_row85
    (Fin.cases v9_row86
    (Fin.cases v9_row87
    (Fin.cases v9_row88
    (Fin.cases v9_row89
    (Fin.cases v9_row90
    (Fin.cases v9_row91
    (Fin.cases v9_row92
    (Fin.cases v9_row93
    (Fin.cases v9_row94
    (Fin.cases v9_row95
    (Fin.cases v9_row96
    (Fin.cases v9_row97
    (Fin.cases v9_row98
    (Fin.cases v9_row99
    (Fin.cases v9_row100
    (Fin.cases v9_row101
    (Fin.cases v9_row102
    (Fin.cases v9_row103
    (Fin.cases v9_row104
    (Fin.cases v9_row105
    (Fin.cases v9_row106
    (Fin.cases v9_row107
    (Fin.cases v9_row108
    (Fin.cases v9_row109
    (Fin.cases v9_row110
    (fun i => Fin.elim0 i))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

/-- Kernel-checked multiplication in the actual matrix algebra. -/
public theorem mul_v9 : v8Matrix * vMatrix = v9Matrix :=
  decode_mul _ _ _ v8_small v_small v9_rows

end Lyons.Atlas111InvolutionWords
