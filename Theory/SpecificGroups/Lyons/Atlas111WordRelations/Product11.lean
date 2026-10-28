module

public import Theory.SpecificGroups.Lyons.Atlas111WordRelations.Data

/-!
# Certified Lyons multiplication: w2 times w2

These 111 row checks certify `w2Matrix * w2Matrix = w4Matrix`.
The carry-free arithmetic soundness theorem gives the matrix identity.
Source: `../Atlas111Source/` and `../Atlas111WordSource/Generate.py`.
All closed certificates are checked by the Lean kernel.
-/

namespace Lyons.Atlas111WordCertificate

set_option Elab.async false

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w4_row0 :
    digitsEq 111 (rowProduct (w2Rows 0) w2Rows 111) (w4Rows 0)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w4_row1 :
    digitsEq 111 (rowProduct (w2Rows 1) w2Rows 111) (w4Rows 1)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w4_row2 :
    digitsEq 111 (rowProduct (w2Rows 2) w2Rows 111) (w4Rows 2)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w4_row3 :
    digitsEq 111 (rowProduct (w2Rows 3) w2Rows 111) (w4Rows 3)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w4_row4 :
    digitsEq 111 (rowProduct (w2Rows 4) w2Rows 111) (w4Rows 4)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w4_row5 :
    digitsEq 111 (rowProduct (w2Rows 5) w2Rows 111) (w4Rows 5)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w4_row6 :
    digitsEq 111 (rowProduct (w2Rows 6) w2Rows 111) (w4Rows 6)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w4_row7 :
    digitsEq 111 (rowProduct (w2Rows 7) w2Rows 111) (w4Rows 7)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w4_row8 :
    digitsEq 111 (rowProduct (w2Rows 8) w2Rows 111) (w4Rows 8)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w4_row9 :
    digitsEq 111 (rowProduct (w2Rows 9) w2Rows 111) (w4Rows 9)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w4_row10 :
    digitsEq 111 (rowProduct (w2Rows 10) w2Rows 111) (w4Rows 10)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w4_row11 :
    digitsEq 111 (rowProduct (w2Rows 11) w2Rows 111) (w4Rows 11)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w4_row12 :
    digitsEq 111 (rowProduct (w2Rows 12) w2Rows 111) (w4Rows 12)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w4_row13 :
    digitsEq 111 (rowProduct (w2Rows 13) w2Rows 111) (w4Rows 13)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w4_row14 :
    digitsEq 111 (rowProduct (w2Rows 14) w2Rows 111) (w4Rows 14)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w4_row15 :
    digitsEq 111 (rowProduct (w2Rows 15) w2Rows 111) (w4Rows 15)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w4_row16 :
    digitsEq 111 (rowProduct (w2Rows 16) w2Rows 111) (w4Rows 16)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w4_row17 :
    digitsEq 111 (rowProduct (w2Rows 17) w2Rows 111) (w4Rows 17)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w4_row18 :
    digitsEq 111 (rowProduct (w2Rows 18) w2Rows 111) (w4Rows 18)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w4_row19 :
    digitsEq 111 (rowProduct (w2Rows 19) w2Rows 111) (w4Rows 19)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w4_row20 :
    digitsEq 111 (rowProduct (w2Rows 20) w2Rows 111) (w4Rows 20)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w4_row21 :
    digitsEq 111 (rowProduct (w2Rows 21) w2Rows 111) (w4Rows 21)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w4_row22 :
    digitsEq 111 (rowProduct (w2Rows 22) w2Rows 111) (w4Rows 22)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w4_row23 :
    digitsEq 111 (rowProduct (w2Rows 23) w2Rows 111) (w4Rows 23)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w4_row24 :
    digitsEq 111 (rowProduct (w2Rows 24) w2Rows 111) (w4Rows 24)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w4_row25 :
    digitsEq 111 (rowProduct (w2Rows 25) w2Rows 111) (w4Rows 25)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w4_row26 :
    digitsEq 111 (rowProduct (w2Rows 26) w2Rows 111) (w4Rows 26)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w4_row27 :
    digitsEq 111 (rowProduct (w2Rows 27) w2Rows 111) (w4Rows 27)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w4_row28 :
    digitsEq 111 (rowProduct (w2Rows 28) w2Rows 111) (w4Rows 28)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w4_row29 :
    digitsEq 111 (rowProduct (w2Rows 29) w2Rows 111) (w4Rows 29)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w4_row30 :
    digitsEq 111 (rowProduct (w2Rows 30) w2Rows 111) (w4Rows 30)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w4_row31 :
    digitsEq 111 (rowProduct (w2Rows 31) w2Rows 111) (w4Rows 31)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w4_row32 :
    digitsEq 111 (rowProduct (w2Rows 32) w2Rows 111) (w4Rows 32)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w4_row33 :
    digitsEq 111 (rowProduct (w2Rows 33) w2Rows 111) (w4Rows 33)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w4_row34 :
    digitsEq 111 (rowProduct (w2Rows 34) w2Rows 111) (w4Rows 34)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w4_row35 :
    digitsEq 111 (rowProduct (w2Rows 35) w2Rows 111) (w4Rows 35)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w4_row36 :
    digitsEq 111 (rowProduct (w2Rows 36) w2Rows 111) (w4Rows 36)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w4_row37 :
    digitsEq 111 (rowProduct (w2Rows 37) w2Rows 111) (w4Rows 37)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w4_row38 :
    digitsEq 111 (rowProduct (w2Rows 38) w2Rows 111) (w4Rows 38)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w4_row39 :
    digitsEq 111 (rowProduct (w2Rows 39) w2Rows 111) (w4Rows 39)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w4_row40 :
    digitsEq 111 (rowProduct (w2Rows 40) w2Rows 111) (w4Rows 40)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w4_row41 :
    digitsEq 111 (rowProduct (w2Rows 41) w2Rows 111) (w4Rows 41)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w4_row42 :
    digitsEq 111 (rowProduct (w2Rows 42) w2Rows 111) (w4Rows 42)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w4_row43 :
    digitsEq 111 (rowProduct (w2Rows 43) w2Rows 111) (w4Rows 43)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w4_row44 :
    digitsEq 111 (rowProduct (w2Rows 44) w2Rows 111) (w4Rows 44)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w4_row45 :
    digitsEq 111 (rowProduct (w2Rows 45) w2Rows 111) (w4Rows 45)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w4_row46 :
    digitsEq 111 (rowProduct (w2Rows 46) w2Rows 111) (w4Rows 46)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w4_row47 :
    digitsEq 111 (rowProduct (w2Rows 47) w2Rows 111) (w4Rows 47)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w4_row48 :
    digitsEq 111 (rowProduct (w2Rows 48) w2Rows 111) (w4Rows 48)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w4_row49 :
    digitsEq 111 (rowProduct (w2Rows 49) w2Rows 111) (w4Rows 49)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w4_row50 :
    digitsEq 111 (rowProduct (w2Rows 50) w2Rows 111) (w4Rows 50)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w4_row51 :
    digitsEq 111 (rowProduct (w2Rows 51) w2Rows 111) (w4Rows 51)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w4_row52 :
    digitsEq 111 (rowProduct (w2Rows 52) w2Rows 111) (w4Rows 52)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w4_row53 :
    digitsEq 111 (rowProduct (w2Rows 53) w2Rows 111) (w4Rows 53)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w4_row54 :
    digitsEq 111 (rowProduct (w2Rows 54) w2Rows 111) (w4Rows 54)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w4_row55 :
    digitsEq 111 (rowProduct (w2Rows 55) w2Rows 111) (w4Rows 55)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w4_row56 :
    digitsEq 111 (rowProduct (w2Rows 56) w2Rows 111) (w4Rows 56)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w4_row57 :
    digitsEq 111 (rowProduct (w2Rows 57) w2Rows 111) (w4Rows 57)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w4_row58 :
    digitsEq 111 (rowProduct (w2Rows 58) w2Rows 111) (w4Rows 58)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w4_row59 :
    digitsEq 111 (rowProduct (w2Rows 59) w2Rows 111) (w4Rows 59)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w4_row60 :
    digitsEq 111 (rowProduct (w2Rows 60) w2Rows 111) (w4Rows 60)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w4_row61 :
    digitsEq 111 (rowProduct (w2Rows 61) w2Rows 111) (w4Rows 61)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w4_row62 :
    digitsEq 111 (rowProduct (w2Rows 62) w2Rows 111) (w4Rows 62)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w4_row63 :
    digitsEq 111 (rowProduct (w2Rows 63) w2Rows 111) (w4Rows 63)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w4_row64 :
    digitsEq 111 (rowProduct (w2Rows 64) w2Rows 111) (w4Rows 64)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w4_row65 :
    digitsEq 111 (rowProduct (w2Rows 65) w2Rows 111) (w4Rows 65)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w4_row66 :
    digitsEq 111 (rowProduct (w2Rows 66) w2Rows 111) (w4Rows 66)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w4_row67 :
    digitsEq 111 (rowProduct (w2Rows 67) w2Rows 111) (w4Rows 67)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w4_row68 :
    digitsEq 111 (rowProduct (w2Rows 68) w2Rows 111) (w4Rows 68)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w4_row69 :
    digitsEq 111 (rowProduct (w2Rows 69) w2Rows 111) (w4Rows 69)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w4_row70 :
    digitsEq 111 (rowProduct (w2Rows 70) w2Rows 111) (w4Rows 70)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w4_row71 :
    digitsEq 111 (rowProduct (w2Rows 71) w2Rows 111) (w4Rows 71)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w4_row72 :
    digitsEq 111 (rowProduct (w2Rows 72) w2Rows 111) (w4Rows 72)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w4_row73 :
    digitsEq 111 (rowProduct (w2Rows 73) w2Rows 111) (w4Rows 73)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w4_row74 :
    digitsEq 111 (rowProduct (w2Rows 74) w2Rows 111) (w4Rows 74)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w4_row75 :
    digitsEq 111 (rowProduct (w2Rows 75) w2Rows 111) (w4Rows 75)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w4_row76 :
    digitsEq 111 (rowProduct (w2Rows 76) w2Rows 111) (w4Rows 76)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w4_row77 :
    digitsEq 111 (rowProduct (w2Rows 77) w2Rows 111) (w4Rows 77)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w4_row78 :
    digitsEq 111 (rowProduct (w2Rows 78) w2Rows 111) (w4Rows 78)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w4_row79 :
    digitsEq 111 (rowProduct (w2Rows 79) w2Rows 111) (w4Rows 79)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w4_row80 :
    digitsEq 111 (rowProduct (w2Rows 80) w2Rows 111) (w4Rows 80)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w4_row81 :
    digitsEq 111 (rowProduct (w2Rows 81) w2Rows 111) (w4Rows 81)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w4_row82 :
    digitsEq 111 (rowProduct (w2Rows 82) w2Rows 111) (w4Rows 82)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w4_row83 :
    digitsEq 111 (rowProduct (w2Rows 83) w2Rows 111) (w4Rows 83)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w4_row84 :
    digitsEq 111 (rowProduct (w2Rows 84) w2Rows 111) (w4Rows 84)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w4_row85 :
    digitsEq 111 (rowProduct (w2Rows 85) w2Rows 111) (w4Rows 85)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w4_row86 :
    digitsEq 111 (rowProduct (w2Rows 86) w2Rows 111) (w4Rows 86)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w4_row87 :
    digitsEq 111 (rowProduct (w2Rows 87) w2Rows 111) (w4Rows 87)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w4_row88 :
    digitsEq 111 (rowProduct (w2Rows 88) w2Rows 111) (w4Rows 88)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w4_row89 :
    digitsEq 111 (rowProduct (w2Rows 89) w2Rows 111) (w4Rows 89)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w4_row90 :
    digitsEq 111 (rowProduct (w2Rows 90) w2Rows 111) (w4Rows 90)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w4_row91 :
    digitsEq 111 (rowProduct (w2Rows 91) w2Rows 111) (w4Rows 91)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w4_row92 :
    digitsEq 111 (rowProduct (w2Rows 92) w2Rows 111) (w4Rows 92)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w4_row93 :
    digitsEq 111 (rowProduct (w2Rows 93) w2Rows 111) (w4Rows 93)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w4_row94 :
    digitsEq 111 (rowProduct (w2Rows 94) w2Rows 111) (w4Rows 94)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w4_row95 :
    digitsEq 111 (rowProduct (w2Rows 95) w2Rows 111) (w4Rows 95)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w4_row96 :
    digitsEq 111 (rowProduct (w2Rows 96) w2Rows 111) (w4Rows 96)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w4_row97 :
    digitsEq 111 (rowProduct (w2Rows 97) w2Rows 111) (w4Rows 97)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w4_row98 :
    digitsEq 111 (rowProduct (w2Rows 98) w2Rows 111) (w4Rows 98)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w4_row99 :
    digitsEq 111 (rowProduct (w2Rows 99) w2Rows 111) (w4Rows 99)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w4_row100 :
    digitsEq 111 (rowProduct (w2Rows 100) w2Rows 111) (w4Rows 100)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w4_row101 :
    digitsEq 111 (rowProduct (w2Rows 101) w2Rows 111) (w4Rows 101)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w4_row102 :
    digitsEq 111 (rowProduct (w2Rows 102) w2Rows 111) (w4Rows 102)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w4_row103 :
    digitsEq 111 (rowProduct (w2Rows 103) w2Rows 111) (w4Rows 103)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w4_row104 :
    digitsEq 111 (rowProduct (w2Rows 104) w2Rows 111) (w4Rows 104)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w4_row105 :
    digitsEq 111 (rowProduct (w2Rows 105) w2Rows 111) (w4Rows 105)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w4_row106 :
    digitsEq 111 (rowProduct (w2Rows 106) w2Rows 111) (w4Rows 106)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w4_row107 :
    digitsEq 111 (rowProduct (w2Rows 107) w2Rows 111) (w4Rows 107)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w4_row108 :
    digitsEq 111 (rowProduct (w2Rows 108) w2Rows 111) (w4Rows 108)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w4_row109 :
    digitsEq 111 (rowProduct (w2Rows 109) w2Rows 111) (w4Rows 109)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w4_row110 :
    digitsEq 111 (rowProduct (w2Rows 110) w2Rows 111) (w4Rows 110)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem w4_rows : ∀ i,
    digitsEq 111 (rowProduct (w2Rows i) w2Rows 111) (w4Rows i) = true :=
  (Fin.cases w4_row0
    (Fin.cases w4_row1
    (Fin.cases w4_row2
    (Fin.cases w4_row3
    (Fin.cases w4_row4
    (Fin.cases w4_row5
    (Fin.cases w4_row6
    (Fin.cases w4_row7
    (Fin.cases w4_row8
    (Fin.cases w4_row9
    (Fin.cases w4_row10
    (Fin.cases w4_row11
    (Fin.cases w4_row12
    (Fin.cases w4_row13
    (Fin.cases w4_row14
    (Fin.cases w4_row15
    (Fin.cases w4_row16
    (Fin.cases w4_row17
    (Fin.cases w4_row18
    (Fin.cases w4_row19
    (Fin.cases w4_row20
    (Fin.cases w4_row21
    (Fin.cases w4_row22
    (Fin.cases w4_row23
    (Fin.cases w4_row24
    (Fin.cases w4_row25
    (Fin.cases w4_row26
    (Fin.cases w4_row27
    (Fin.cases w4_row28
    (Fin.cases w4_row29
    (Fin.cases w4_row30
    (Fin.cases w4_row31
    (Fin.cases w4_row32
    (Fin.cases w4_row33
    (Fin.cases w4_row34
    (Fin.cases w4_row35
    (Fin.cases w4_row36
    (Fin.cases w4_row37
    (Fin.cases w4_row38
    (Fin.cases w4_row39
    (Fin.cases w4_row40
    (Fin.cases w4_row41
    (Fin.cases w4_row42
    (Fin.cases w4_row43
    (Fin.cases w4_row44
    (Fin.cases w4_row45
    (Fin.cases w4_row46
    (Fin.cases w4_row47
    (Fin.cases w4_row48
    (Fin.cases w4_row49
    (Fin.cases w4_row50
    (Fin.cases w4_row51
    (Fin.cases w4_row52
    (Fin.cases w4_row53
    (Fin.cases w4_row54
    (Fin.cases w4_row55
    (Fin.cases w4_row56
    (Fin.cases w4_row57
    (Fin.cases w4_row58
    (Fin.cases w4_row59
    (Fin.cases w4_row60
    (Fin.cases w4_row61
    (Fin.cases w4_row62
    (Fin.cases w4_row63
    (Fin.cases w4_row64
    (Fin.cases w4_row65
    (Fin.cases w4_row66
    (Fin.cases w4_row67
    (Fin.cases w4_row68
    (Fin.cases w4_row69
    (Fin.cases w4_row70
    (Fin.cases w4_row71
    (Fin.cases w4_row72
    (Fin.cases w4_row73
    (Fin.cases w4_row74
    (Fin.cases w4_row75
    (Fin.cases w4_row76
    (Fin.cases w4_row77
    (Fin.cases w4_row78
    (Fin.cases w4_row79
    (Fin.cases w4_row80
    (Fin.cases w4_row81
    (Fin.cases w4_row82
    (Fin.cases w4_row83
    (Fin.cases w4_row84
    (Fin.cases w4_row85
    (Fin.cases w4_row86
    (Fin.cases w4_row87
    (Fin.cases w4_row88
    (Fin.cases w4_row89
    (Fin.cases w4_row90
    (Fin.cases w4_row91
    (Fin.cases w4_row92
    (Fin.cases w4_row93
    (Fin.cases w4_row94
    (Fin.cases w4_row95
    (Fin.cases w4_row96
    (Fin.cases w4_row97
    (Fin.cases w4_row98
    (Fin.cases w4_row99
    (Fin.cases w4_row100
    (Fin.cases w4_row101
    (Fin.cases w4_row102
    (Fin.cases w4_row103
    (Fin.cases w4_row104
    (Fin.cases w4_row105
    (Fin.cases w4_row106
    (Fin.cases w4_row107
    (Fin.cases w4_row108
    (Fin.cases w4_row109
    (Fin.cases w4_row110
    (fun i => Fin.elim0 i))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

/-- Checked multiplication in the actual matrix algebra. -/
public theorem mul_w4 : w2Matrix * w2Matrix = w4Matrix :=
  decode_mul _ _ _ w2_small w2_small w4_rows

end Lyons.Atlas111WordCertificate
