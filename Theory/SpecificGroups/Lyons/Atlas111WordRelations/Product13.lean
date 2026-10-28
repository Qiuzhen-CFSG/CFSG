module

public import Theory.SpecificGroups.Lyons.Atlas111WordRelations.Data

/-!
# Certified Lyons multiplication: w8 times w8

These 111 row checks certify `w8Matrix * w8Matrix = w16Matrix`.
The carry-free arithmetic soundness theorem gives the matrix identity.
Source: `../Atlas111Source/` and `../Atlas111WordSource/Generate.py`.
All closed certificates are checked by the Lean kernel.
-/

namespace Lyons.Atlas111WordCertificate

set_option Elab.async false

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w16_row0 :
    digitsEq 111 (rowProduct (w8Rows 0) w8Rows 111) (w16Rows 0)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w16_row1 :
    digitsEq 111 (rowProduct (w8Rows 1) w8Rows 111) (w16Rows 1)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w16_row2 :
    digitsEq 111 (rowProduct (w8Rows 2) w8Rows 111) (w16Rows 2)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w16_row3 :
    digitsEq 111 (rowProduct (w8Rows 3) w8Rows 111) (w16Rows 3)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w16_row4 :
    digitsEq 111 (rowProduct (w8Rows 4) w8Rows 111) (w16Rows 4)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w16_row5 :
    digitsEq 111 (rowProduct (w8Rows 5) w8Rows 111) (w16Rows 5)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w16_row6 :
    digitsEq 111 (rowProduct (w8Rows 6) w8Rows 111) (w16Rows 6)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w16_row7 :
    digitsEq 111 (rowProduct (w8Rows 7) w8Rows 111) (w16Rows 7)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w16_row8 :
    digitsEq 111 (rowProduct (w8Rows 8) w8Rows 111) (w16Rows 8)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w16_row9 :
    digitsEq 111 (rowProduct (w8Rows 9) w8Rows 111) (w16Rows 9)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w16_row10 :
    digitsEq 111 (rowProduct (w8Rows 10) w8Rows 111) (w16Rows 10)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w16_row11 :
    digitsEq 111 (rowProduct (w8Rows 11) w8Rows 111) (w16Rows 11)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w16_row12 :
    digitsEq 111 (rowProduct (w8Rows 12) w8Rows 111) (w16Rows 12)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w16_row13 :
    digitsEq 111 (rowProduct (w8Rows 13) w8Rows 111) (w16Rows 13)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w16_row14 :
    digitsEq 111 (rowProduct (w8Rows 14) w8Rows 111) (w16Rows 14)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w16_row15 :
    digitsEq 111 (rowProduct (w8Rows 15) w8Rows 111) (w16Rows 15)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w16_row16 :
    digitsEq 111 (rowProduct (w8Rows 16) w8Rows 111) (w16Rows 16)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w16_row17 :
    digitsEq 111 (rowProduct (w8Rows 17) w8Rows 111) (w16Rows 17)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w16_row18 :
    digitsEq 111 (rowProduct (w8Rows 18) w8Rows 111) (w16Rows 18)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w16_row19 :
    digitsEq 111 (rowProduct (w8Rows 19) w8Rows 111) (w16Rows 19)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w16_row20 :
    digitsEq 111 (rowProduct (w8Rows 20) w8Rows 111) (w16Rows 20)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w16_row21 :
    digitsEq 111 (rowProduct (w8Rows 21) w8Rows 111) (w16Rows 21)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w16_row22 :
    digitsEq 111 (rowProduct (w8Rows 22) w8Rows 111) (w16Rows 22)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w16_row23 :
    digitsEq 111 (rowProduct (w8Rows 23) w8Rows 111) (w16Rows 23)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w16_row24 :
    digitsEq 111 (rowProduct (w8Rows 24) w8Rows 111) (w16Rows 24)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w16_row25 :
    digitsEq 111 (rowProduct (w8Rows 25) w8Rows 111) (w16Rows 25)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w16_row26 :
    digitsEq 111 (rowProduct (w8Rows 26) w8Rows 111) (w16Rows 26)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w16_row27 :
    digitsEq 111 (rowProduct (w8Rows 27) w8Rows 111) (w16Rows 27)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w16_row28 :
    digitsEq 111 (rowProduct (w8Rows 28) w8Rows 111) (w16Rows 28)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w16_row29 :
    digitsEq 111 (rowProduct (w8Rows 29) w8Rows 111) (w16Rows 29)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w16_row30 :
    digitsEq 111 (rowProduct (w8Rows 30) w8Rows 111) (w16Rows 30)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w16_row31 :
    digitsEq 111 (rowProduct (w8Rows 31) w8Rows 111) (w16Rows 31)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w16_row32 :
    digitsEq 111 (rowProduct (w8Rows 32) w8Rows 111) (w16Rows 32)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w16_row33 :
    digitsEq 111 (rowProduct (w8Rows 33) w8Rows 111) (w16Rows 33)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w16_row34 :
    digitsEq 111 (rowProduct (w8Rows 34) w8Rows 111) (w16Rows 34)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w16_row35 :
    digitsEq 111 (rowProduct (w8Rows 35) w8Rows 111) (w16Rows 35)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w16_row36 :
    digitsEq 111 (rowProduct (w8Rows 36) w8Rows 111) (w16Rows 36)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w16_row37 :
    digitsEq 111 (rowProduct (w8Rows 37) w8Rows 111) (w16Rows 37)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w16_row38 :
    digitsEq 111 (rowProduct (w8Rows 38) w8Rows 111) (w16Rows 38)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w16_row39 :
    digitsEq 111 (rowProduct (w8Rows 39) w8Rows 111) (w16Rows 39)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w16_row40 :
    digitsEq 111 (rowProduct (w8Rows 40) w8Rows 111) (w16Rows 40)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w16_row41 :
    digitsEq 111 (rowProduct (w8Rows 41) w8Rows 111) (w16Rows 41)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w16_row42 :
    digitsEq 111 (rowProduct (w8Rows 42) w8Rows 111) (w16Rows 42)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w16_row43 :
    digitsEq 111 (rowProduct (w8Rows 43) w8Rows 111) (w16Rows 43)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w16_row44 :
    digitsEq 111 (rowProduct (w8Rows 44) w8Rows 111) (w16Rows 44)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w16_row45 :
    digitsEq 111 (rowProduct (w8Rows 45) w8Rows 111) (w16Rows 45)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w16_row46 :
    digitsEq 111 (rowProduct (w8Rows 46) w8Rows 111) (w16Rows 46)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w16_row47 :
    digitsEq 111 (rowProduct (w8Rows 47) w8Rows 111) (w16Rows 47)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w16_row48 :
    digitsEq 111 (rowProduct (w8Rows 48) w8Rows 111) (w16Rows 48)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w16_row49 :
    digitsEq 111 (rowProduct (w8Rows 49) w8Rows 111) (w16Rows 49)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w16_row50 :
    digitsEq 111 (rowProduct (w8Rows 50) w8Rows 111) (w16Rows 50)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w16_row51 :
    digitsEq 111 (rowProduct (w8Rows 51) w8Rows 111) (w16Rows 51)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w16_row52 :
    digitsEq 111 (rowProduct (w8Rows 52) w8Rows 111) (w16Rows 52)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w16_row53 :
    digitsEq 111 (rowProduct (w8Rows 53) w8Rows 111) (w16Rows 53)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w16_row54 :
    digitsEq 111 (rowProduct (w8Rows 54) w8Rows 111) (w16Rows 54)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w16_row55 :
    digitsEq 111 (rowProduct (w8Rows 55) w8Rows 111) (w16Rows 55)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w16_row56 :
    digitsEq 111 (rowProduct (w8Rows 56) w8Rows 111) (w16Rows 56)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w16_row57 :
    digitsEq 111 (rowProduct (w8Rows 57) w8Rows 111) (w16Rows 57)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w16_row58 :
    digitsEq 111 (rowProduct (w8Rows 58) w8Rows 111) (w16Rows 58)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w16_row59 :
    digitsEq 111 (rowProduct (w8Rows 59) w8Rows 111) (w16Rows 59)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w16_row60 :
    digitsEq 111 (rowProduct (w8Rows 60) w8Rows 111) (w16Rows 60)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w16_row61 :
    digitsEq 111 (rowProduct (w8Rows 61) w8Rows 111) (w16Rows 61)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w16_row62 :
    digitsEq 111 (rowProduct (w8Rows 62) w8Rows 111) (w16Rows 62)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w16_row63 :
    digitsEq 111 (rowProduct (w8Rows 63) w8Rows 111) (w16Rows 63)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w16_row64 :
    digitsEq 111 (rowProduct (w8Rows 64) w8Rows 111) (w16Rows 64)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w16_row65 :
    digitsEq 111 (rowProduct (w8Rows 65) w8Rows 111) (w16Rows 65)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w16_row66 :
    digitsEq 111 (rowProduct (w8Rows 66) w8Rows 111) (w16Rows 66)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w16_row67 :
    digitsEq 111 (rowProduct (w8Rows 67) w8Rows 111) (w16Rows 67)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w16_row68 :
    digitsEq 111 (rowProduct (w8Rows 68) w8Rows 111) (w16Rows 68)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w16_row69 :
    digitsEq 111 (rowProduct (w8Rows 69) w8Rows 111) (w16Rows 69)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w16_row70 :
    digitsEq 111 (rowProduct (w8Rows 70) w8Rows 111) (w16Rows 70)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w16_row71 :
    digitsEq 111 (rowProduct (w8Rows 71) w8Rows 111) (w16Rows 71)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w16_row72 :
    digitsEq 111 (rowProduct (w8Rows 72) w8Rows 111) (w16Rows 72)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w16_row73 :
    digitsEq 111 (rowProduct (w8Rows 73) w8Rows 111) (w16Rows 73)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w16_row74 :
    digitsEq 111 (rowProduct (w8Rows 74) w8Rows 111) (w16Rows 74)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w16_row75 :
    digitsEq 111 (rowProduct (w8Rows 75) w8Rows 111) (w16Rows 75)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w16_row76 :
    digitsEq 111 (rowProduct (w8Rows 76) w8Rows 111) (w16Rows 76)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w16_row77 :
    digitsEq 111 (rowProduct (w8Rows 77) w8Rows 111) (w16Rows 77)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w16_row78 :
    digitsEq 111 (rowProduct (w8Rows 78) w8Rows 111) (w16Rows 78)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w16_row79 :
    digitsEq 111 (rowProduct (w8Rows 79) w8Rows 111) (w16Rows 79)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w16_row80 :
    digitsEq 111 (rowProduct (w8Rows 80) w8Rows 111) (w16Rows 80)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w16_row81 :
    digitsEq 111 (rowProduct (w8Rows 81) w8Rows 111) (w16Rows 81)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w16_row82 :
    digitsEq 111 (rowProduct (w8Rows 82) w8Rows 111) (w16Rows 82)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w16_row83 :
    digitsEq 111 (rowProduct (w8Rows 83) w8Rows 111) (w16Rows 83)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w16_row84 :
    digitsEq 111 (rowProduct (w8Rows 84) w8Rows 111) (w16Rows 84)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w16_row85 :
    digitsEq 111 (rowProduct (w8Rows 85) w8Rows 111) (w16Rows 85)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w16_row86 :
    digitsEq 111 (rowProduct (w8Rows 86) w8Rows 111) (w16Rows 86)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w16_row87 :
    digitsEq 111 (rowProduct (w8Rows 87) w8Rows 111) (w16Rows 87)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w16_row88 :
    digitsEq 111 (rowProduct (w8Rows 88) w8Rows 111) (w16Rows 88)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w16_row89 :
    digitsEq 111 (rowProduct (w8Rows 89) w8Rows 111) (w16Rows 89)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w16_row90 :
    digitsEq 111 (rowProduct (w8Rows 90) w8Rows 111) (w16Rows 90)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w16_row91 :
    digitsEq 111 (rowProduct (w8Rows 91) w8Rows 111) (w16Rows 91)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w16_row92 :
    digitsEq 111 (rowProduct (w8Rows 92) w8Rows 111) (w16Rows 92)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w16_row93 :
    digitsEq 111 (rowProduct (w8Rows 93) w8Rows 111) (w16Rows 93)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w16_row94 :
    digitsEq 111 (rowProduct (w8Rows 94) w8Rows 111) (w16Rows 94)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w16_row95 :
    digitsEq 111 (rowProduct (w8Rows 95) w8Rows 111) (w16Rows 95)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w16_row96 :
    digitsEq 111 (rowProduct (w8Rows 96) w8Rows 111) (w16Rows 96)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w16_row97 :
    digitsEq 111 (rowProduct (w8Rows 97) w8Rows 111) (w16Rows 97)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w16_row98 :
    digitsEq 111 (rowProduct (w8Rows 98) w8Rows 111) (w16Rows 98)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w16_row99 :
    digitsEq 111 (rowProduct (w8Rows 99) w8Rows 111) (w16Rows 99)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w16_row100 :
    digitsEq 111 (rowProduct (w8Rows 100) w8Rows 111) (w16Rows 100)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w16_row101 :
    digitsEq 111 (rowProduct (w8Rows 101) w8Rows 111) (w16Rows 101)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w16_row102 :
    digitsEq 111 (rowProduct (w8Rows 102) w8Rows 111) (w16Rows 102)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w16_row103 :
    digitsEq 111 (rowProduct (w8Rows 103) w8Rows 111) (w16Rows 103)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w16_row104 :
    digitsEq 111 (rowProduct (w8Rows 104) w8Rows 111) (w16Rows 104)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w16_row105 :
    digitsEq 111 (rowProduct (w8Rows 105) w8Rows 111) (w16Rows 105)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w16_row106 :
    digitsEq 111 (rowProduct (w8Rows 106) w8Rows 111) (w16Rows 106)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w16_row107 :
    digitsEq 111 (rowProduct (w8Rows 107) w8Rows 111) (w16Rows 107)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w16_row108 :
    digitsEq 111 (rowProduct (w8Rows 108) w8Rows 111) (w16Rows 108)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w16_row109 :
    digitsEq 111 (rowProduct (w8Rows 109) w8Rows 111) (w16Rows 109)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w16_row110 :
    digitsEq 111 (rowProduct (w8Rows 110) w8Rows 111) (w16Rows 110)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem w16_rows : ∀ i,
    digitsEq 111 (rowProduct (w8Rows i) w8Rows 111) (w16Rows i) = true :=
  (Fin.cases w16_row0
    (Fin.cases w16_row1
    (Fin.cases w16_row2
    (Fin.cases w16_row3
    (Fin.cases w16_row4
    (Fin.cases w16_row5
    (Fin.cases w16_row6
    (Fin.cases w16_row7
    (Fin.cases w16_row8
    (Fin.cases w16_row9
    (Fin.cases w16_row10
    (Fin.cases w16_row11
    (Fin.cases w16_row12
    (Fin.cases w16_row13
    (Fin.cases w16_row14
    (Fin.cases w16_row15
    (Fin.cases w16_row16
    (Fin.cases w16_row17
    (Fin.cases w16_row18
    (Fin.cases w16_row19
    (Fin.cases w16_row20
    (Fin.cases w16_row21
    (Fin.cases w16_row22
    (Fin.cases w16_row23
    (Fin.cases w16_row24
    (Fin.cases w16_row25
    (Fin.cases w16_row26
    (Fin.cases w16_row27
    (Fin.cases w16_row28
    (Fin.cases w16_row29
    (Fin.cases w16_row30
    (Fin.cases w16_row31
    (Fin.cases w16_row32
    (Fin.cases w16_row33
    (Fin.cases w16_row34
    (Fin.cases w16_row35
    (Fin.cases w16_row36
    (Fin.cases w16_row37
    (Fin.cases w16_row38
    (Fin.cases w16_row39
    (Fin.cases w16_row40
    (Fin.cases w16_row41
    (Fin.cases w16_row42
    (Fin.cases w16_row43
    (Fin.cases w16_row44
    (Fin.cases w16_row45
    (Fin.cases w16_row46
    (Fin.cases w16_row47
    (Fin.cases w16_row48
    (Fin.cases w16_row49
    (Fin.cases w16_row50
    (Fin.cases w16_row51
    (Fin.cases w16_row52
    (Fin.cases w16_row53
    (Fin.cases w16_row54
    (Fin.cases w16_row55
    (Fin.cases w16_row56
    (Fin.cases w16_row57
    (Fin.cases w16_row58
    (Fin.cases w16_row59
    (Fin.cases w16_row60
    (Fin.cases w16_row61
    (Fin.cases w16_row62
    (Fin.cases w16_row63
    (Fin.cases w16_row64
    (Fin.cases w16_row65
    (Fin.cases w16_row66
    (Fin.cases w16_row67
    (Fin.cases w16_row68
    (Fin.cases w16_row69
    (Fin.cases w16_row70
    (Fin.cases w16_row71
    (Fin.cases w16_row72
    (Fin.cases w16_row73
    (Fin.cases w16_row74
    (Fin.cases w16_row75
    (Fin.cases w16_row76
    (Fin.cases w16_row77
    (Fin.cases w16_row78
    (Fin.cases w16_row79
    (Fin.cases w16_row80
    (Fin.cases w16_row81
    (Fin.cases w16_row82
    (Fin.cases w16_row83
    (Fin.cases w16_row84
    (Fin.cases w16_row85
    (Fin.cases w16_row86
    (Fin.cases w16_row87
    (Fin.cases w16_row88
    (Fin.cases w16_row89
    (Fin.cases w16_row90
    (Fin.cases w16_row91
    (Fin.cases w16_row92
    (Fin.cases w16_row93
    (Fin.cases w16_row94
    (Fin.cases w16_row95
    (Fin.cases w16_row96
    (Fin.cases w16_row97
    (Fin.cases w16_row98
    (Fin.cases w16_row99
    (Fin.cases w16_row100
    (Fin.cases w16_row101
    (Fin.cases w16_row102
    (Fin.cases w16_row103
    (Fin.cases w16_row104
    (Fin.cases w16_row105
    (Fin.cases w16_row106
    (Fin.cases w16_row107
    (Fin.cases w16_row108
    (Fin.cases w16_row109
    (Fin.cases w16_row110
    (fun i => Fin.elim0 i))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

/-- Checked multiplication in the actual matrix algebra. -/
public theorem mul_w16 : w8Matrix * w8Matrix = w16Matrix :=
  decode_mul _ _ _ w8_small w8_small w16_rows

end Lyons.Atlas111WordCertificate
