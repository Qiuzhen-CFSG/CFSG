module

public import Theory.SpecificGroups.Lyons.Atlas111InvolutionWords.Data

/-!
# Involution word multiplication: a times u

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
private theorem v_row0 :
    digitsEq 111 (rowProduct (aRows 0) uRows 111) (vRows 0)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem v_row1 :
    digitsEq 111 (rowProduct (aRows 1) uRows 111) (vRows 1)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem v_row2 :
    digitsEq 111 (rowProduct (aRows 2) uRows 111) (vRows 2)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem v_row3 :
    digitsEq 111 (rowProduct (aRows 3) uRows 111) (vRows 3)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem v_row4 :
    digitsEq 111 (rowProduct (aRows 4) uRows 111) (vRows 4)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem v_row5 :
    digitsEq 111 (rowProduct (aRows 5) uRows 111) (vRows 5)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem v_row6 :
    digitsEq 111 (rowProduct (aRows 6) uRows 111) (vRows 6)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem v_row7 :
    digitsEq 111 (rowProduct (aRows 7) uRows 111) (vRows 7)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem v_row8 :
    digitsEq 111 (rowProduct (aRows 8) uRows 111) (vRows 8)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem v_row9 :
    digitsEq 111 (rowProduct (aRows 9) uRows 111) (vRows 9)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem v_row10 :
    digitsEq 111 (rowProduct (aRows 10) uRows 111) (vRows 10)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem v_row11 :
    digitsEq 111 (rowProduct (aRows 11) uRows 111) (vRows 11)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem v_row12 :
    digitsEq 111 (rowProduct (aRows 12) uRows 111) (vRows 12)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem v_row13 :
    digitsEq 111 (rowProduct (aRows 13) uRows 111) (vRows 13)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem v_row14 :
    digitsEq 111 (rowProduct (aRows 14) uRows 111) (vRows 14)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem v_row15 :
    digitsEq 111 (rowProduct (aRows 15) uRows 111) (vRows 15)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem v_row16 :
    digitsEq 111 (rowProduct (aRows 16) uRows 111) (vRows 16)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem v_row17 :
    digitsEq 111 (rowProduct (aRows 17) uRows 111) (vRows 17)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem v_row18 :
    digitsEq 111 (rowProduct (aRows 18) uRows 111) (vRows 18)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem v_row19 :
    digitsEq 111 (rowProduct (aRows 19) uRows 111) (vRows 19)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem v_row20 :
    digitsEq 111 (rowProduct (aRows 20) uRows 111) (vRows 20)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem v_row21 :
    digitsEq 111 (rowProduct (aRows 21) uRows 111) (vRows 21)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem v_row22 :
    digitsEq 111 (rowProduct (aRows 22) uRows 111) (vRows 22)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem v_row23 :
    digitsEq 111 (rowProduct (aRows 23) uRows 111) (vRows 23)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem v_row24 :
    digitsEq 111 (rowProduct (aRows 24) uRows 111) (vRows 24)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem v_row25 :
    digitsEq 111 (rowProduct (aRows 25) uRows 111) (vRows 25)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem v_row26 :
    digitsEq 111 (rowProduct (aRows 26) uRows 111) (vRows 26)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem v_row27 :
    digitsEq 111 (rowProduct (aRows 27) uRows 111) (vRows 27)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem v_row28 :
    digitsEq 111 (rowProduct (aRows 28) uRows 111) (vRows 28)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem v_row29 :
    digitsEq 111 (rowProduct (aRows 29) uRows 111) (vRows 29)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem v_row30 :
    digitsEq 111 (rowProduct (aRows 30) uRows 111) (vRows 30)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem v_row31 :
    digitsEq 111 (rowProduct (aRows 31) uRows 111) (vRows 31)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem v_row32 :
    digitsEq 111 (rowProduct (aRows 32) uRows 111) (vRows 32)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem v_row33 :
    digitsEq 111 (rowProduct (aRows 33) uRows 111) (vRows 33)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem v_row34 :
    digitsEq 111 (rowProduct (aRows 34) uRows 111) (vRows 34)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem v_row35 :
    digitsEq 111 (rowProduct (aRows 35) uRows 111) (vRows 35)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem v_row36 :
    digitsEq 111 (rowProduct (aRows 36) uRows 111) (vRows 36)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem v_row37 :
    digitsEq 111 (rowProduct (aRows 37) uRows 111) (vRows 37)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem v_row38 :
    digitsEq 111 (rowProduct (aRows 38) uRows 111) (vRows 38)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem v_row39 :
    digitsEq 111 (rowProduct (aRows 39) uRows 111) (vRows 39)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem v_row40 :
    digitsEq 111 (rowProduct (aRows 40) uRows 111) (vRows 40)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem v_row41 :
    digitsEq 111 (rowProduct (aRows 41) uRows 111) (vRows 41)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem v_row42 :
    digitsEq 111 (rowProduct (aRows 42) uRows 111) (vRows 42)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem v_row43 :
    digitsEq 111 (rowProduct (aRows 43) uRows 111) (vRows 43)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem v_row44 :
    digitsEq 111 (rowProduct (aRows 44) uRows 111) (vRows 44)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem v_row45 :
    digitsEq 111 (rowProduct (aRows 45) uRows 111) (vRows 45)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem v_row46 :
    digitsEq 111 (rowProduct (aRows 46) uRows 111) (vRows 46)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem v_row47 :
    digitsEq 111 (rowProduct (aRows 47) uRows 111) (vRows 47)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem v_row48 :
    digitsEq 111 (rowProduct (aRows 48) uRows 111) (vRows 48)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem v_row49 :
    digitsEq 111 (rowProduct (aRows 49) uRows 111) (vRows 49)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem v_row50 :
    digitsEq 111 (rowProduct (aRows 50) uRows 111) (vRows 50)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem v_row51 :
    digitsEq 111 (rowProduct (aRows 51) uRows 111) (vRows 51)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem v_row52 :
    digitsEq 111 (rowProduct (aRows 52) uRows 111) (vRows 52)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem v_row53 :
    digitsEq 111 (rowProduct (aRows 53) uRows 111) (vRows 53)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem v_row54 :
    digitsEq 111 (rowProduct (aRows 54) uRows 111) (vRows 54)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem v_row55 :
    digitsEq 111 (rowProduct (aRows 55) uRows 111) (vRows 55)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem v_row56 :
    digitsEq 111 (rowProduct (aRows 56) uRows 111) (vRows 56)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem v_row57 :
    digitsEq 111 (rowProduct (aRows 57) uRows 111) (vRows 57)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem v_row58 :
    digitsEq 111 (rowProduct (aRows 58) uRows 111) (vRows 58)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem v_row59 :
    digitsEq 111 (rowProduct (aRows 59) uRows 111) (vRows 59)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem v_row60 :
    digitsEq 111 (rowProduct (aRows 60) uRows 111) (vRows 60)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem v_row61 :
    digitsEq 111 (rowProduct (aRows 61) uRows 111) (vRows 61)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem v_row62 :
    digitsEq 111 (rowProduct (aRows 62) uRows 111) (vRows 62)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem v_row63 :
    digitsEq 111 (rowProduct (aRows 63) uRows 111) (vRows 63)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem v_row64 :
    digitsEq 111 (rowProduct (aRows 64) uRows 111) (vRows 64)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem v_row65 :
    digitsEq 111 (rowProduct (aRows 65) uRows 111) (vRows 65)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem v_row66 :
    digitsEq 111 (rowProduct (aRows 66) uRows 111) (vRows 66)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem v_row67 :
    digitsEq 111 (rowProduct (aRows 67) uRows 111) (vRows 67)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem v_row68 :
    digitsEq 111 (rowProduct (aRows 68) uRows 111) (vRows 68)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem v_row69 :
    digitsEq 111 (rowProduct (aRows 69) uRows 111) (vRows 69)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem v_row70 :
    digitsEq 111 (rowProduct (aRows 70) uRows 111) (vRows 70)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem v_row71 :
    digitsEq 111 (rowProduct (aRows 71) uRows 111) (vRows 71)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem v_row72 :
    digitsEq 111 (rowProduct (aRows 72) uRows 111) (vRows 72)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem v_row73 :
    digitsEq 111 (rowProduct (aRows 73) uRows 111) (vRows 73)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem v_row74 :
    digitsEq 111 (rowProduct (aRows 74) uRows 111) (vRows 74)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem v_row75 :
    digitsEq 111 (rowProduct (aRows 75) uRows 111) (vRows 75)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem v_row76 :
    digitsEq 111 (rowProduct (aRows 76) uRows 111) (vRows 76)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem v_row77 :
    digitsEq 111 (rowProduct (aRows 77) uRows 111) (vRows 77)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem v_row78 :
    digitsEq 111 (rowProduct (aRows 78) uRows 111) (vRows 78)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem v_row79 :
    digitsEq 111 (rowProduct (aRows 79) uRows 111) (vRows 79)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem v_row80 :
    digitsEq 111 (rowProduct (aRows 80) uRows 111) (vRows 80)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem v_row81 :
    digitsEq 111 (rowProduct (aRows 81) uRows 111) (vRows 81)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem v_row82 :
    digitsEq 111 (rowProduct (aRows 82) uRows 111) (vRows 82)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem v_row83 :
    digitsEq 111 (rowProduct (aRows 83) uRows 111) (vRows 83)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem v_row84 :
    digitsEq 111 (rowProduct (aRows 84) uRows 111) (vRows 84)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem v_row85 :
    digitsEq 111 (rowProduct (aRows 85) uRows 111) (vRows 85)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem v_row86 :
    digitsEq 111 (rowProduct (aRows 86) uRows 111) (vRows 86)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem v_row87 :
    digitsEq 111 (rowProduct (aRows 87) uRows 111) (vRows 87)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem v_row88 :
    digitsEq 111 (rowProduct (aRows 88) uRows 111) (vRows 88)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem v_row89 :
    digitsEq 111 (rowProduct (aRows 89) uRows 111) (vRows 89)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem v_row90 :
    digitsEq 111 (rowProduct (aRows 90) uRows 111) (vRows 90)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem v_row91 :
    digitsEq 111 (rowProduct (aRows 91) uRows 111) (vRows 91)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem v_row92 :
    digitsEq 111 (rowProduct (aRows 92) uRows 111) (vRows 92)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem v_row93 :
    digitsEq 111 (rowProduct (aRows 93) uRows 111) (vRows 93)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem v_row94 :
    digitsEq 111 (rowProduct (aRows 94) uRows 111) (vRows 94)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem v_row95 :
    digitsEq 111 (rowProduct (aRows 95) uRows 111) (vRows 95)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem v_row96 :
    digitsEq 111 (rowProduct (aRows 96) uRows 111) (vRows 96)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem v_row97 :
    digitsEq 111 (rowProduct (aRows 97) uRows 111) (vRows 97)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem v_row98 :
    digitsEq 111 (rowProduct (aRows 98) uRows 111) (vRows 98)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem v_row99 :
    digitsEq 111 (rowProduct (aRows 99) uRows 111) (vRows 99)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem v_row100 :
    digitsEq 111 (rowProduct (aRows 100) uRows 111) (vRows 100)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem v_row101 :
    digitsEq 111 (rowProduct (aRows 101) uRows 111) (vRows 101)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem v_row102 :
    digitsEq 111 (rowProduct (aRows 102) uRows 111) (vRows 102)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem v_row103 :
    digitsEq 111 (rowProduct (aRows 103) uRows 111) (vRows 103)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem v_row104 :
    digitsEq 111 (rowProduct (aRows 104) uRows 111) (vRows 104)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem v_row105 :
    digitsEq 111 (rowProduct (aRows 105) uRows 111) (vRows 105)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem v_row106 :
    digitsEq 111 (rowProduct (aRows 106) uRows 111) (vRows 106)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem v_row107 :
    digitsEq 111 (rowProduct (aRows 107) uRows 111) (vRows 107)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem v_row108 :
    digitsEq 111 (rowProduct (aRows 108) uRows 111) (vRows 108)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem v_row109 :
    digitsEq 111 (rowProduct (aRows 109) uRows 111) (vRows 109)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem v_row110 :
    digitsEq 111 (rowProduct (aRows 110) uRows 111) (vRows 110)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem v_rows : ∀ i,
    digitsEq 111 (rowProduct (aRows i) uRows 111) (vRows i) = true :=
  (Fin.cases v_row0
    (Fin.cases v_row1
    (Fin.cases v_row2
    (Fin.cases v_row3
    (Fin.cases v_row4
    (Fin.cases v_row5
    (Fin.cases v_row6
    (Fin.cases v_row7
    (Fin.cases v_row8
    (Fin.cases v_row9
    (Fin.cases v_row10
    (Fin.cases v_row11
    (Fin.cases v_row12
    (Fin.cases v_row13
    (Fin.cases v_row14
    (Fin.cases v_row15
    (Fin.cases v_row16
    (Fin.cases v_row17
    (Fin.cases v_row18
    (Fin.cases v_row19
    (Fin.cases v_row20
    (Fin.cases v_row21
    (Fin.cases v_row22
    (Fin.cases v_row23
    (Fin.cases v_row24
    (Fin.cases v_row25
    (Fin.cases v_row26
    (Fin.cases v_row27
    (Fin.cases v_row28
    (Fin.cases v_row29
    (Fin.cases v_row30
    (Fin.cases v_row31
    (Fin.cases v_row32
    (Fin.cases v_row33
    (Fin.cases v_row34
    (Fin.cases v_row35
    (Fin.cases v_row36
    (Fin.cases v_row37
    (Fin.cases v_row38
    (Fin.cases v_row39
    (Fin.cases v_row40
    (Fin.cases v_row41
    (Fin.cases v_row42
    (Fin.cases v_row43
    (Fin.cases v_row44
    (Fin.cases v_row45
    (Fin.cases v_row46
    (Fin.cases v_row47
    (Fin.cases v_row48
    (Fin.cases v_row49
    (Fin.cases v_row50
    (Fin.cases v_row51
    (Fin.cases v_row52
    (Fin.cases v_row53
    (Fin.cases v_row54
    (Fin.cases v_row55
    (Fin.cases v_row56
    (Fin.cases v_row57
    (Fin.cases v_row58
    (Fin.cases v_row59
    (Fin.cases v_row60
    (Fin.cases v_row61
    (Fin.cases v_row62
    (Fin.cases v_row63
    (Fin.cases v_row64
    (Fin.cases v_row65
    (Fin.cases v_row66
    (Fin.cases v_row67
    (Fin.cases v_row68
    (Fin.cases v_row69
    (Fin.cases v_row70
    (Fin.cases v_row71
    (Fin.cases v_row72
    (Fin.cases v_row73
    (Fin.cases v_row74
    (Fin.cases v_row75
    (Fin.cases v_row76
    (Fin.cases v_row77
    (Fin.cases v_row78
    (Fin.cases v_row79
    (Fin.cases v_row80
    (Fin.cases v_row81
    (Fin.cases v_row82
    (Fin.cases v_row83
    (Fin.cases v_row84
    (Fin.cases v_row85
    (Fin.cases v_row86
    (Fin.cases v_row87
    (Fin.cases v_row88
    (Fin.cases v_row89
    (Fin.cases v_row90
    (Fin.cases v_row91
    (Fin.cases v_row92
    (Fin.cases v_row93
    (Fin.cases v_row94
    (Fin.cases v_row95
    (Fin.cases v_row96
    (Fin.cases v_row97
    (Fin.cases v_row98
    (Fin.cases v_row99
    (Fin.cases v_row100
    (Fin.cases v_row101
    (Fin.cases v_row102
    (Fin.cases v_row103
    (Fin.cases v_row104
    (Fin.cases v_row105
    (Fin.cases v_row106
    (Fin.cases v_row107
    (Fin.cases v_row108
    (Fin.cases v_row109
    (Fin.cases v_row110
    (fun i => Fin.elim0 i))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

/-- Kernel-checked multiplication in the actual matrix algebra. -/
public theorem mul_v : aMatrix * uMatrix = vMatrix :=
  decode_mul _ _ _ a_small u_small v_rows

end Lyons.Atlas111InvolutionWords
