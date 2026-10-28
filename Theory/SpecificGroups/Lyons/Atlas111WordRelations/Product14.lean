module

public import Theory.SpecificGroups.Lyons.Atlas111WordRelations.Data

/-!
# Certified Lyons multiplication: w16 times w16

These 111 row checks certify `w16Matrix * w16Matrix = w32Matrix`.
The carry-free arithmetic soundness theorem gives the matrix identity.
Source: `../Atlas111Source/` and `../Atlas111WordSource/Generate.py`.
All closed certificates are checked by the Lean kernel.
-/

namespace Lyons.Atlas111WordCertificate

set_option Elab.async false

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w32_row0 :
    digitsEq 111 (rowProduct (w16Rows 0) w16Rows 111) (w32Rows 0)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w32_row1 :
    digitsEq 111 (rowProduct (w16Rows 1) w16Rows 111) (w32Rows 1)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w32_row2 :
    digitsEq 111 (rowProduct (w16Rows 2) w16Rows 111) (w32Rows 2)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w32_row3 :
    digitsEq 111 (rowProduct (w16Rows 3) w16Rows 111) (w32Rows 3)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w32_row4 :
    digitsEq 111 (rowProduct (w16Rows 4) w16Rows 111) (w32Rows 4)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w32_row5 :
    digitsEq 111 (rowProduct (w16Rows 5) w16Rows 111) (w32Rows 5)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w32_row6 :
    digitsEq 111 (rowProduct (w16Rows 6) w16Rows 111) (w32Rows 6)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w32_row7 :
    digitsEq 111 (rowProduct (w16Rows 7) w16Rows 111) (w32Rows 7)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w32_row8 :
    digitsEq 111 (rowProduct (w16Rows 8) w16Rows 111) (w32Rows 8)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w32_row9 :
    digitsEq 111 (rowProduct (w16Rows 9) w16Rows 111) (w32Rows 9)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w32_row10 :
    digitsEq 111 (rowProduct (w16Rows 10) w16Rows 111) (w32Rows 10)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w32_row11 :
    digitsEq 111 (rowProduct (w16Rows 11) w16Rows 111) (w32Rows 11)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w32_row12 :
    digitsEq 111 (rowProduct (w16Rows 12) w16Rows 111) (w32Rows 12)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w32_row13 :
    digitsEq 111 (rowProduct (w16Rows 13) w16Rows 111) (w32Rows 13)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w32_row14 :
    digitsEq 111 (rowProduct (w16Rows 14) w16Rows 111) (w32Rows 14)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w32_row15 :
    digitsEq 111 (rowProduct (w16Rows 15) w16Rows 111) (w32Rows 15)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w32_row16 :
    digitsEq 111 (rowProduct (w16Rows 16) w16Rows 111) (w32Rows 16)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w32_row17 :
    digitsEq 111 (rowProduct (w16Rows 17) w16Rows 111) (w32Rows 17)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w32_row18 :
    digitsEq 111 (rowProduct (w16Rows 18) w16Rows 111) (w32Rows 18)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w32_row19 :
    digitsEq 111 (rowProduct (w16Rows 19) w16Rows 111) (w32Rows 19)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w32_row20 :
    digitsEq 111 (rowProduct (w16Rows 20) w16Rows 111) (w32Rows 20)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w32_row21 :
    digitsEq 111 (rowProduct (w16Rows 21) w16Rows 111) (w32Rows 21)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w32_row22 :
    digitsEq 111 (rowProduct (w16Rows 22) w16Rows 111) (w32Rows 22)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w32_row23 :
    digitsEq 111 (rowProduct (w16Rows 23) w16Rows 111) (w32Rows 23)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w32_row24 :
    digitsEq 111 (rowProduct (w16Rows 24) w16Rows 111) (w32Rows 24)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w32_row25 :
    digitsEq 111 (rowProduct (w16Rows 25) w16Rows 111) (w32Rows 25)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w32_row26 :
    digitsEq 111 (rowProduct (w16Rows 26) w16Rows 111) (w32Rows 26)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w32_row27 :
    digitsEq 111 (rowProduct (w16Rows 27) w16Rows 111) (w32Rows 27)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w32_row28 :
    digitsEq 111 (rowProduct (w16Rows 28) w16Rows 111) (w32Rows 28)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w32_row29 :
    digitsEq 111 (rowProduct (w16Rows 29) w16Rows 111) (w32Rows 29)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w32_row30 :
    digitsEq 111 (rowProduct (w16Rows 30) w16Rows 111) (w32Rows 30)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w32_row31 :
    digitsEq 111 (rowProduct (w16Rows 31) w16Rows 111) (w32Rows 31)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w32_row32 :
    digitsEq 111 (rowProduct (w16Rows 32) w16Rows 111) (w32Rows 32)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w32_row33 :
    digitsEq 111 (rowProduct (w16Rows 33) w16Rows 111) (w32Rows 33)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w32_row34 :
    digitsEq 111 (rowProduct (w16Rows 34) w16Rows 111) (w32Rows 34)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w32_row35 :
    digitsEq 111 (rowProduct (w16Rows 35) w16Rows 111) (w32Rows 35)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w32_row36 :
    digitsEq 111 (rowProduct (w16Rows 36) w16Rows 111) (w32Rows 36)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w32_row37 :
    digitsEq 111 (rowProduct (w16Rows 37) w16Rows 111) (w32Rows 37)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w32_row38 :
    digitsEq 111 (rowProduct (w16Rows 38) w16Rows 111) (w32Rows 38)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w32_row39 :
    digitsEq 111 (rowProduct (w16Rows 39) w16Rows 111) (w32Rows 39)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w32_row40 :
    digitsEq 111 (rowProduct (w16Rows 40) w16Rows 111) (w32Rows 40)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w32_row41 :
    digitsEq 111 (rowProduct (w16Rows 41) w16Rows 111) (w32Rows 41)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w32_row42 :
    digitsEq 111 (rowProduct (w16Rows 42) w16Rows 111) (w32Rows 42)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w32_row43 :
    digitsEq 111 (rowProduct (w16Rows 43) w16Rows 111) (w32Rows 43)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w32_row44 :
    digitsEq 111 (rowProduct (w16Rows 44) w16Rows 111) (w32Rows 44)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w32_row45 :
    digitsEq 111 (rowProduct (w16Rows 45) w16Rows 111) (w32Rows 45)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w32_row46 :
    digitsEq 111 (rowProduct (w16Rows 46) w16Rows 111) (w32Rows 46)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w32_row47 :
    digitsEq 111 (rowProduct (w16Rows 47) w16Rows 111) (w32Rows 47)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w32_row48 :
    digitsEq 111 (rowProduct (w16Rows 48) w16Rows 111) (w32Rows 48)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w32_row49 :
    digitsEq 111 (rowProduct (w16Rows 49) w16Rows 111) (w32Rows 49)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w32_row50 :
    digitsEq 111 (rowProduct (w16Rows 50) w16Rows 111) (w32Rows 50)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w32_row51 :
    digitsEq 111 (rowProduct (w16Rows 51) w16Rows 111) (w32Rows 51)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w32_row52 :
    digitsEq 111 (rowProduct (w16Rows 52) w16Rows 111) (w32Rows 52)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w32_row53 :
    digitsEq 111 (rowProduct (w16Rows 53) w16Rows 111) (w32Rows 53)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w32_row54 :
    digitsEq 111 (rowProduct (w16Rows 54) w16Rows 111) (w32Rows 54)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w32_row55 :
    digitsEq 111 (rowProduct (w16Rows 55) w16Rows 111) (w32Rows 55)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w32_row56 :
    digitsEq 111 (rowProduct (w16Rows 56) w16Rows 111) (w32Rows 56)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w32_row57 :
    digitsEq 111 (rowProduct (w16Rows 57) w16Rows 111) (w32Rows 57)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w32_row58 :
    digitsEq 111 (rowProduct (w16Rows 58) w16Rows 111) (w32Rows 58)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w32_row59 :
    digitsEq 111 (rowProduct (w16Rows 59) w16Rows 111) (w32Rows 59)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w32_row60 :
    digitsEq 111 (rowProduct (w16Rows 60) w16Rows 111) (w32Rows 60)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w32_row61 :
    digitsEq 111 (rowProduct (w16Rows 61) w16Rows 111) (w32Rows 61)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w32_row62 :
    digitsEq 111 (rowProduct (w16Rows 62) w16Rows 111) (w32Rows 62)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w32_row63 :
    digitsEq 111 (rowProduct (w16Rows 63) w16Rows 111) (w32Rows 63)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w32_row64 :
    digitsEq 111 (rowProduct (w16Rows 64) w16Rows 111) (w32Rows 64)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w32_row65 :
    digitsEq 111 (rowProduct (w16Rows 65) w16Rows 111) (w32Rows 65)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w32_row66 :
    digitsEq 111 (rowProduct (w16Rows 66) w16Rows 111) (w32Rows 66)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w32_row67 :
    digitsEq 111 (rowProduct (w16Rows 67) w16Rows 111) (w32Rows 67)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w32_row68 :
    digitsEq 111 (rowProduct (w16Rows 68) w16Rows 111) (w32Rows 68)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w32_row69 :
    digitsEq 111 (rowProduct (w16Rows 69) w16Rows 111) (w32Rows 69)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w32_row70 :
    digitsEq 111 (rowProduct (w16Rows 70) w16Rows 111) (w32Rows 70)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w32_row71 :
    digitsEq 111 (rowProduct (w16Rows 71) w16Rows 111) (w32Rows 71)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w32_row72 :
    digitsEq 111 (rowProduct (w16Rows 72) w16Rows 111) (w32Rows 72)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w32_row73 :
    digitsEq 111 (rowProduct (w16Rows 73) w16Rows 111) (w32Rows 73)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w32_row74 :
    digitsEq 111 (rowProduct (w16Rows 74) w16Rows 111) (w32Rows 74)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w32_row75 :
    digitsEq 111 (rowProduct (w16Rows 75) w16Rows 111) (w32Rows 75)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w32_row76 :
    digitsEq 111 (rowProduct (w16Rows 76) w16Rows 111) (w32Rows 76)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w32_row77 :
    digitsEq 111 (rowProduct (w16Rows 77) w16Rows 111) (w32Rows 77)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w32_row78 :
    digitsEq 111 (rowProduct (w16Rows 78) w16Rows 111) (w32Rows 78)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w32_row79 :
    digitsEq 111 (rowProduct (w16Rows 79) w16Rows 111) (w32Rows 79)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w32_row80 :
    digitsEq 111 (rowProduct (w16Rows 80) w16Rows 111) (w32Rows 80)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w32_row81 :
    digitsEq 111 (rowProduct (w16Rows 81) w16Rows 111) (w32Rows 81)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w32_row82 :
    digitsEq 111 (rowProduct (w16Rows 82) w16Rows 111) (w32Rows 82)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w32_row83 :
    digitsEq 111 (rowProduct (w16Rows 83) w16Rows 111) (w32Rows 83)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w32_row84 :
    digitsEq 111 (rowProduct (w16Rows 84) w16Rows 111) (w32Rows 84)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w32_row85 :
    digitsEq 111 (rowProduct (w16Rows 85) w16Rows 111) (w32Rows 85)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w32_row86 :
    digitsEq 111 (rowProduct (w16Rows 86) w16Rows 111) (w32Rows 86)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w32_row87 :
    digitsEq 111 (rowProduct (w16Rows 87) w16Rows 111) (w32Rows 87)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w32_row88 :
    digitsEq 111 (rowProduct (w16Rows 88) w16Rows 111) (w32Rows 88)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w32_row89 :
    digitsEq 111 (rowProduct (w16Rows 89) w16Rows 111) (w32Rows 89)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w32_row90 :
    digitsEq 111 (rowProduct (w16Rows 90) w16Rows 111) (w32Rows 90)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w32_row91 :
    digitsEq 111 (rowProduct (w16Rows 91) w16Rows 111) (w32Rows 91)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w32_row92 :
    digitsEq 111 (rowProduct (w16Rows 92) w16Rows 111) (w32Rows 92)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w32_row93 :
    digitsEq 111 (rowProduct (w16Rows 93) w16Rows 111) (w32Rows 93)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w32_row94 :
    digitsEq 111 (rowProduct (w16Rows 94) w16Rows 111) (w32Rows 94)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w32_row95 :
    digitsEq 111 (rowProduct (w16Rows 95) w16Rows 111) (w32Rows 95)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w32_row96 :
    digitsEq 111 (rowProduct (w16Rows 96) w16Rows 111) (w32Rows 96)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w32_row97 :
    digitsEq 111 (rowProduct (w16Rows 97) w16Rows 111) (w32Rows 97)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w32_row98 :
    digitsEq 111 (rowProduct (w16Rows 98) w16Rows 111) (w32Rows 98)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w32_row99 :
    digitsEq 111 (rowProduct (w16Rows 99) w16Rows 111) (w32Rows 99)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w32_row100 :
    digitsEq 111 (rowProduct (w16Rows 100) w16Rows 111) (w32Rows 100)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w32_row101 :
    digitsEq 111 (rowProduct (w16Rows 101) w16Rows 111) (w32Rows 101)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w32_row102 :
    digitsEq 111 (rowProduct (w16Rows 102) w16Rows 111) (w32Rows 102)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w32_row103 :
    digitsEq 111 (rowProduct (w16Rows 103) w16Rows 111) (w32Rows 103)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w32_row104 :
    digitsEq 111 (rowProduct (w16Rows 104) w16Rows 111) (w32Rows 104)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w32_row105 :
    digitsEq 111 (rowProduct (w16Rows 105) w16Rows 111) (w32Rows 105)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w32_row106 :
    digitsEq 111 (rowProduct (w16Rows 106) w16Rows 111) (w32Rows 106)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w32_row107 :
    digitsEq 111 (rowProduct (w16Rows 107) w16Rows 111) (w32Rows 107)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w32_row108 :
    digitsEq 111 (rowProduct (w16Rows 108) w16Rows 111) (w32Rows 108)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w32_row109 :
    digitsEq 111 (rowProduct (w16Rows 109) w16Rows 111) (w32Rows 109)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w32_row110 :
    digitsEq 111 (rowProduct (w16Rows 110) w16Rows 111) (w32Rows 110)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem w32_rows : ∀ i,
    digitsEq 111 (rowProduct (w16Rows i) w16Rows 111) (w32Rows i) = true :=
  (Fin.cases w32_row0
    (Fin.cases w32_row1
    (Fin.cases w32_row2
    (Fin.cases w32_row3
    (Fin.cases w32_row4
    (Fin.cases w32_row5
    (Fin.cases w32_row6
    (Fin.cases w32_row7
    (Fin.cases w32_row8
    (Fin.cases w32_row9
    (Fin.cases w32_row10
    (Fin.cases w32_row11
    (Fin.cases w32_row12
    (Fin.cases w32_row13
    (Fin.cases w32_row14
    (Fin.cases w32_row15
    (Fin.cases w32_row16
    (Fin.cases w32_row17
    (Fin.cases w32_row18
    (Fin.cases w32_row19
    (Fin.cases w32_row20
    (Fin.cases w32_row21
    (Fin.cases w32_row22
    (Fin.cases w32_row23
    (Fin.cases w32_row24
    (Fin.cases w32_row25
    (Fin.cases w32_row26
    (Fin.cases w32_row27
    (Fin.cases w32_row28
    (Fin.cases w32_row29
    (Fin.cases w32_row30
    (Fin.cases w32_row31
    (Fin.cases w32_row32
    (Fin.cases w32_row33
    (Fin.cases w32_row34
    (Fin.cases w32_row35
    (Fin.cases w32_row36
    (Fin.cases w32_row37
    (Fin.cases w32_row38
    (Fin.cases w32_row39
    (Fin.cases w32_row40
    (Fin.cases w32_row41
    (Fin.cases w32_row42
    (Fin.cases w32_row43
    (Fin.cases w32_row44
    (Fin.cases w32_row45
    (Fin.cases w32_row46
    (Fin.cases w32_row47
    (Fin.cases w32_row48
    (Fin.cases w32_row49
    (Fin.cases w32_row50
    (Fin.cases w32_row51
    (Fin.cases w32_row52
    (Fin.cases w32_row53
    (Fin.cases w32_row54
    (Fin.cases w32_row55
    (Fin.cases w32_row56
    (Fin.cases w32_row57
    (Fin.cases w32_row58
    (Fin.cases w32_row59
    (Fin.cases w32_row60
    (Fin.cases w32_row61
    (Fin.cases w32_row62
    (Fin.cases w32_row63
    (Fin.cases w32_row64
    (Fin.cases w32_row65
    (Fin.cases w32_row66
    (Fin.cases w32_row67
    (Fin.cases w32_row68
    (Fin.cases w32_row69
    (Fin.cases w32_row70
    (Fin.cases w32_row71
    (Fin.cases w32_row72
    (Fin.cases w32_row73
    (Fin.cases w32_row74
    (Fin.cases w32_row75
    (Fin.cases w32_row76
    (Fin.cases w32_row77
    (Fin.cases w32_row78
    (Fin.cases w32_row79
    (Fin.cases w32_row80
    (Fin.cases w32_row81
    (Fin.cases w32_row82
    (Fin.cases w32_row83
    (Fin.cases w32_row84
    (Fin.cases w32_row85
    (Fin.cases w32_row86
    (Fin.cases w32_row87
    (Fin.cases w32_row88
    (Fin.cases w32_row89
    (Fin.cases w32_row90
    (Fin.cases w32_row91
    (Fin.cases w32_row92
    (Fin.cases w32_row93
    (Fin.cases w32_row94
    (Fin.cases w32_row95
    (Fin.cases w32_row96
    (Fin.cases w32_row97
    (Fin.cases w32_row98
    (Fin.cases w32_row99
    (Fin.cases w32_row100
    (Fin.cases w32_row101
    (Fin.cases w32_row102
    (Fin.cases w32_row103
    (Fin.cases w32_row104
    (Fin.cases w32_row105
    (Fin.cases w32_row106
    (Fin.cases w32_row107
    (Fin.cases w32_row108
    (Fin.cases w32_row109
    (Fin.cases w32_row110
    (fun i => Fin.elim0 i))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

/-- Checked multiplication in the actual matrix algebra. -/
public theorem mul_w32 : w16Matrix * w16Matrix = w32Matrix :=
  decode_mul _ _ _ w16_small w16_small w32_rows

end Lyons.Atlas111WordCertificate
