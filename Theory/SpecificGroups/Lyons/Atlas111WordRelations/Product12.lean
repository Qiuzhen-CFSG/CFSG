module

public import Theory.SpecificGroups.Lyons.Atlas111WordRelations.Data

/-!
# Certified Lyons multiplication: w4 times w4

These 111 row checks certify `w4Matrix * w4Matrix = w8Matrix`.
The carry-free arithmetic soundness theorem gives the matrix identity.
Source: `../Atlas111Source/` and `../Atlas111WordSource/Generate.py`.
All closed certificates are checked by the Lean kernel.
-/

namespace Lyons.Atlas111WordCertificate

set_option Elab.async false

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w8_row0 :
    digitsEq 111 (rowProduct (w4Rows 0) w4Rows 111) (w8Rows 0)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w8_row1 :
    digitsEq 111 (rowProduct (w4Rows 1) w4Rows 111) (w8Rows 1)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w8_row2 :
    digitsEq 111 (rowProduct (w4Rows 2) w4Rows 111) (w8Rows 2)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w8_row3 :
    digitsEq 111 (rowProduct (w4Rows 3) w4Rows 111) (w8Rows 3)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w8_row4 :
    digitsEq 111 (rowProduct (w4Rows 4) w4Rows 111) (w8Rows 4)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w8_row5 :
    digitsEq 111 (rowProduct (w4Rows 5) w4Rows 111) (w8Rows 5)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w8_row6 :
    digitsEq 111 (rowProduct (w4Rows 6) w4Rows 111) (w8Rows 6)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w8_row7 :
    digitsEq 111 (rowProduct (w4Rows 7) w4Rows 111) (w8Rows 7)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w8_row8 :
    digitsEq 111 (rowProduct (w4Rows 8) w4Rows 111) (w8Rows 8)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w8_row9 :
    digitsEq 111 (rowProduct (w4Rows 9) w4Rows 111) (w8Rows 9)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w8_row10 :
    digitsEq 111 (rowProduct (w4Rows 10) w4Rows 111) (w8Rows 10)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w8_row11 :
    digitsEq 111 (rowProduct (w4Rows 11) w4Rows 111) (w8Rows 11)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w8_row12 :
    digitsEq 111 (rowProduct (w4Rows 12) w4Rows 111) (w8Rows 12)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w8_row13 :
    digitsEq 111 (rowProduct (w4Rows 13) w4Rows 111) (w8Rows 13)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w8_row14 :
    digitsEq 111 (rowProduct (w4Rows 14) w4Rows 111) (w8Rows 14)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w8_row15 :
    digitsEq 111 (rowProduct (w4Rows 15) w4Rows 111) (w8Rows 15)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w8_row16 :
    digitsEq 111 (rowProduct (w4Rows 16) w4Rows 111) (w8Rows 16)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w8_row17 :
    digitsEq 111 (rowProduct (w4Rows 17) w4Rows 111) (w8Rows 17)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w8_row18 :
    digitsEq 111 (rowProduct (w4Rows 18) w4Rows 111) (w8Rows 18)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w8_row19 :
    digitsEq 111 (rowProduct (w4Rows 19) w4Rows 111) (w8Rows 19)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w8_row20 :
    digitsEq 111 (rowProduct (w4Rows 20) w4Rows 111) (w8Rows 20)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w8_row21 :
    digitsEq 111 (rowProduct (w4Rows 21) w4Rows 111) (w8Rows 21)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w8_row22 :
    digitsEq 111 (rowProduct (w4Rows 22) w4Rows 111) (w8Rows 22)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w8_row23 :
    digitsEq 111 (rowProduct (w4Rows 23) w4Rows 111) (w8Rows 23)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w8_row24 :
    digitsEq 111 (rowProduct (w4Rows 24) w4Rows 111) (w8Rows 24)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w8_row25 :
    digitsEq 111 (rowProduct (w4Rows 25) w4Rows 111) (w8Rows 25)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w8_row26 :
    digitsEq 111 (rowProduct (w4Rows 26) w4Rows 111) (w8Rows 26)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w8_row27 :
    digitsEq 111 (rowProduct (w4Rows 27) w4Rows 111) (w8Rows 27)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w8_row28 :
    digitsEq 111 (rowProduct (w4Rows 28) w4Rows 111) (w8Rows 28)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w8_row29 :
    digitsEq 111 (rowProduct (w4Rows 29) w4Rows 111) (w8Rows 29)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w8_row30 :
    digitsEq 111 (rowProduct (w4Rows 30) w4Rows 111) (w8Rows 30)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w8_row31 :
    digitsEq 111 (rowProduct (w4Rows 31) w4Rows 111) (w8Rows 31)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w8_row32 :
    digitsEq 111 (rowProduct (w4Rows 32) w4Rows 111) (w8Rows 32)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w8_row33 :
    digitsEq 111 (rowProduct (w4Rows 33) w4Rows 111) (w8Rows 33)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w8_row34 :
    digitsEq 111 (rowProduct (w4Rows 34) w4Rows 111) (w8Rows 34)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w8_row35 :
    digitsEq 111 (rowProduct (w4Rows 35) w4Rows 111) (w8Rows 35)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w8_row36 :
    digitsEq 111 (rowProduct (w4Rows 36) w4Rows 111) (w8Rows 36)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w8_row37 :
    digitsEq 111 (rowProduct (w4Rows 37) w4Rows 111) (w8Rows 37)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w8_row38 :
    digitsEq 111 (rowProduct (w4Rows 38) w4Rows 111) (w8Rows 38)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w8_row39 :
    digitsEq 111 (rowProduct (w4Rows 39) w4Rows 111) (w8Rows 39)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w8_row40 :
    digitsEq 111 (rowProduct (w4Rows 40) w4Rows 111) (w8Rows 40)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w8_row41 :
    digitsEq 111 (rowProduct (w4Rows 41) w4Rows 111) (w8Rows 41)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w8_row42 :
    digitsEq 111 (rowProduct (w4Rows 42) w4Rows 111) (w8Rows 42)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w8_row43 :
    digitsEq 111 (rowProduct (w4Rows 43) w4Rows 111) (w8Rows 43)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w8_row44 :
    digitsEq 111 (rowProduct (w4Rows 44) w4Rows 111) (w8Rows 44)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w8_row45 :
    digitsEq 111 (rowProduct (w4Rows 45) w4Rows 111) (w8Rows 45)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w8_row46 :
    digitsEq 111 (rowProduct (w4Rows 46) w4Rows 111) (w8Rows 46)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w8_row47 :
    digitsEq 111 (rowProduct (w4Rows 47) w4Rows 111) (w8Rows 47)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w8_row48 :
    digitsEq 111 (rowProduct (w4Rows 48) w4Rows 111) (w8Rows 48)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w8_row49 :
    digitsEq 111 (rowProduct (w4Rows 49) w4Rows 111) (w8Rows 49)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w8_row50 :
    digitsEq 111 (rowProduct (w4Rows 50) w4Rows 111) (w8Rows 50)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w8_row51 :
    digitsEq 111 (rowProduct (w4Rows 51) w4Rows 111) (w8Rows 51)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w8_row52 :
    digitsEq 111 (rowProduct (w4Rows 52) w4Rows 111) (w8Rows 52)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w8_row53 :
    digitsEq 111 (rowProduct (w4Rows 53) w4Rows 111) (w8Rows 53)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w8_row54 :
    digitsEq 111 (rowProduct (w4Rows 54) w4Rows 111) (w8Rows 54)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w8_row55 :
    digitsEq 111 (rowProduct (w4Rows 55) w4Rows 111) (w8Rows 55)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w8_row56 :
    digitsEq 111 (rowProduct (w4Rows 56) w4Rows 111) (w8Rows 56)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w8_row57 :
    digitsEq 111 (rowProduct (w4Rows 57) w4Rows 111) (w8Rows 57)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w8_row58 :
    digitsEq 111 (rowProduct (w4Rows 58) w4Rows 111) (w8Rows 58)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w8_row59 :
    digitsEq 111 (rowProduct (w4Rows 59) w4Rows 111) (w8Rows 59)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w8_row60 :
    digitsEq 111 (rowProduct (w4Rows 60) w4Rows 111) (w8Rows 60)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w8_row61 :
    digitsEq 111 (rowProduct (w4Rows 61) w4Rows 111) (w8Rows 61)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w8_row62 :
    digitsEq 111 (rowProduct (w4Rows 62) w4Rows 111) (w8Rows 62)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w8_row63 :
    digitsEq 111 (rowProduct (w4Rows 63) w4Rows 111) (w8Rows 63)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w8_row64 :
    digitsEq 111 (rowProduct (w4Rows 64) w4Rows 111) (w8Rows 64)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w8_row65 :
    digitsEq 111 (rowProduct (w4Rows 65) w4Rows 111) (w8Rows 65)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w8_row66 :
    digitsEq 111 (rowProduct (w4Rows 66) w4Rows 111) (w8Rows 66)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w8_row67 :
    digitsEq 111 (rowProduct (w4Rows 67) w4Rows 111) (w8Rows 67)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w8_row68 :
    digitsEq 111 (rowProduct (w4Rows 68) w4Rows 111) (w8Rows 68)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w8_row69 :
    digitsEq 111 (rowProduct (w4Rows 69) w4Rows 111) (w8Rows 69)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w8_row70 :
    digitsEq 111 (rowProduct (w4Rows 70) w4Rows 111) (w8Rows 70)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w8_row71 :
    digitsEq 111 (rowProduct (w4Rows 71) w4Rows 111) (w8Rows 71)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w8_row72 :
    digitsEq 111 (rowProduct (w4Rows 72) w4Rows 111) (w8Rows 72)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w8_row73 :
    digitsEq 111 (rowProduct (w4Rows 73) w4Rows 111) (w8Rows 73)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w8_row74 :
    digitsEq 111 (rowProduct (w4Rows 74) w4Rows 111) (w8Rows 74)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w8_row75 :
    digitsEq 111 (rowProduct (w4Rows 75) w4Rows 111) (w8Rows 75)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w8_row76 :
    digitsEq 111 (rowProduct (w4Rows 76) w4Rows 111) (w8Rows 76)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w8_row77 :
    digitsEq 111 (rowProduct (w4Rows 77) w4Rows 111) (w8Rows 77)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w8_row78 :
    digitsEq 111 (rowProduct (w4Rows 78) w4Rows 111) (w8Rows 78)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w8_row79 :
    digitsEq 111 (rowProduct (w4Rows 79) w4Rows 111) (w8Rows 79)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w8_row80 :
    digitsEq 111 (rowProduct (w4Rows 80) w4Rows 111) (w8Rows 80)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w8_row81 :
    digitsEq 111 (rowProduct (w4Rows 81) w4Rows 111) (w8Rows 81)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w8_row82 :
    digitsEq 111 (rowProduct (w4Rows 82) w4Rows 111) (w8Rows 82)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w8_row83 :
    digitsEq 111 (rowProduct (w4Rows 83) w4Rows 111) (w8Rows 83)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w8_row84 :
    digitsEq 111 (rowProduct (w4Rows 84) w4Rows 111) (w8Rows 84)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w8_row85 :
    digitsEq 111 (rowProduct (w4Rows 85) w4Rows 111) (w8Rows 85)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w8_row86 :
    digitsEq 111 (rowProduct (w4Rows 86) w4Rows 111) (w8Rows 86)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w8_row87 :
    digitsEq 111 (rowProduct (w4Rows 87) w4Rows 111) (w8Rows 87)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w8_row88 :
    digitsEq 111 (rowProduct (w4Rows 88) w4Rows 111) (w8Rows 88)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w8_row89 :
    digitsEq 111 (rowProduct (w4Rows 89) w4Rows 111) (w8Rows 89)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w8_row90 :
    digitsEq 111 (rowProduct (w4Rows 90) w4Rows 111) (w8Rows 90)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w8_row91 :
    digitsEq 111 (rowProduct (w4Rows 91) w4Rows 111) (w8Rows 91)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w8_row92 :
    digitsEq 111 (rowProduct (w4Rows 92) w4Rows 111) (w8Rows 92)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w8_row93 :
    digitsEq 111 (rowProduct (w4Rows 93) w4Rows 111) (w8Rows 93)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w8_row94 :
    digitsEq 111 (rowProduct (w4Rows 94) w4Rows 111) (w8Rows 94)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w8_row95 :
    digitsEq 111 (rowProduct (w4Rows 95) w4Rows 111) (w8Rows 95)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w8_row96 :
    digitsEq 111 (rowProduct (w4Rows 96) w4Rows 111) (w8Rows 96)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w8_row97 :
    digitsEq 111 (rowProduct (w4Rows 97) w4Rows 111) (w8Rows 97)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w8_row98 :
    digitsEq 111 (rowProduct (w4Rows 98) w4Rows 111) (w8Rows 98)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w8_row99 :
    digitsEq 111 (rowProduct (w4Rows 99) w4Rows 111) (w8Rows 99)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w8_row100 :
    digitsEq 111 (rowProduct (w4Rows 100) w4Rows 111) (w8Rows 100)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w8_row101 :
    digitsEq 111 (rowProduct (w4Rows 101) w4Rows 111) (w8Rows 101)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w8_row102 :
    digitsEq 111 (rowProduct (w4Rows 102) w4Rows 111) (w8Rows 102)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w8_row103 :
    digitsEq 111 (rowProduct (w4Rows 103) w4Rows 111) (w8Rows 103)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w8_row104 :
    digitsEq 111 (rowProduct (w4Rows 104) w4Rows 111) (w8Rows 104)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w8_row105 :
    digitsEq 111 (rowProduct (w4Rows 105) w4Rows 111) (w8Rows 105)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w8_row106 :
    digitsEq 111 (rowProduct (w4Rows 106) w4Rows 111) (w8Rows 106)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w8_row107 :
    digitsEq 111 (rowProduct (w4Rows 107) w4Rows 111) (w8Rows 107)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w8_row108 :
    digitsEq 111 (rowProduct (w4Rows 108) w4Rows 111) (w8Rows 108)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w8_row109 :
    digitsEq 111 (rowProduct (w4Rows 109) w4Rows 111) (w8Rows 109)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w8_row110 :
    digitsEq 111 (rowProduct (w4Rows 110) w4Rows 111) (w8Rows 110)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem w8_rows : ∀ i,
    digitsEq 111 (rowProduct (w4Rows i) w4Rows 111) (w8Rows i) = true :=
  (Fin.cases w8_row0
    (Fin.cases w8_row1
    (Fin.cases w8_row2
    (Fin.cases w8_row3
    (Fin.cases w8_row4
    (Fin.cases w8_row5
    (Fin.cases w8_row6
    (Fin.cases w8_row7
    (Fin.cases w8_row8
    (Fin.cases w8_row9
    (Fin.cases w8_row10
    (Fin.cases w8_row11
    (Fin.cases w8_row12
    (Fin.cases w8_row13
    (Fin.cases w8_row14
    (Fin.cases w8_row15
    (Fin.cases w8_row16
    (Fin.cases w8_row17
    (Fin.cases w8_row18
    (Fin.cases w8_row19
    (Fin.cases w8_row20
    (Fin.cases w8_row21
    (Fin.cases w8_row22
    (Fin.cases w8_row23
    (Fin.cases w8_row24
    (Fin.cases w8_row25
    (Fin.cases w8_row26
    (Fin.cases w8_row27
    (Fin.cases w8_row28
    (Fin.cases w8_row29
    (Fin.cases w8_row30
    (Fin.cases w8_row31
    (Fin.cases w8_row32
    (Fin.cases w8_row33
    (Fin.cases w8_row34
    (Fin.cases w8_row35
    (Fin.cases w8_row36
    (Fin.cases w8_row37
    (Fin.cases w8_row38
    (Fin.cases w8_row39
    (Fin.cases w8_row40
    (Fin.cases w8_row41
    (Fin.cases w8_row42
    (Fin.cases w8_row43
    (Fin.cases w8_row44
    (Fin.cases w8_row45
    (Fin.cases w8_row46
    (Fin.cases w8_row47
    (Fin.cases w8_row48
    (Fin.cases w8_row49
    (Fin.cases w8_row50
    (Fin.cases w8_row51
    (Fin.cases w8_row52
    (Fin.cases w8_row53
    (Fin.cases w8_row54
    (Fin.cases w8_row55
    (Fin.cases w8_row56
    (Fin.cases w8_row57
    (Fin.cases w8_row58
    (Fin.cases w8_row59
    (Fin.cases w8_row60
    (Fin.cases w8_row61
    (Fin.cases w8_row62
    (Fin.cases w8_row63
    (Fin.cases w8_row64
    (Fin.cases w8_row65
    (Fin.cases w8_row66
    (Fin.cases w8_row67
    (Fin.cases w8_row68
    (Fin.cases w8_row69
    (Fin.cases w8_row70
    (Fin.cases w8_row71
    (Fin.cases w8_row72
    (Fin.cases w8_row73
    (Fin.cases w8_row74
    (Fin.cases w8_row75
    (Fin.cases w8_row76
    (Fin.cases w8_row77
    (Fin.cases w8_row78
    (Fin.cases w8_row79
    (Fin.cases w8_row80
    (Fin.cases w8_row81
    (Fin.cases w8_row82
    (Fin.cases w8_row83
    (Fin.cases w8_row84
    (Fin.cases w8_row85
    (Fin.cases w8_row86
    (Fin.cases w8_row87
    (Fin.cases w8_row88
    (Fin.cases w8_row89
    (Fin.cases w8_row90
    (Fin.cases w8_row91
    (Fin.cases w8_row92
    (Fin.cases w8_row93
    (Fin.cases w8_row94
    (Fin.cases w8_row95
    (Fin.cases w8_row96
    (Fin.cases w8_row97
    (Fin.cases w8_row98
    (Fin.cases w8_row99
    (Fin.cases w8_row100
    (Fin.cases w8_row101
    (Fin.cases w8_row102
    (Fin.cases w8_row103
    (Fin.cases w8_row104
    (Fin.cases w8_row105
    (Fin.cases w8_row106
    (Fin.cases w8_row107
    (Fin.cases w8_row108
    (Fin.cases w8_row109
    (Fin.cases w8_row110
    (fun i => Fin.elim0 i))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

/-- Checked multiplication in the actual matrix algebra. -/
public theorem mul_w8 : w4Matrix * w4Matrix = w8Matrix :=
  decode_mul _ _ _ w4_small w4_small w8_rows

end Lyons.Atlas111WordCertificate
