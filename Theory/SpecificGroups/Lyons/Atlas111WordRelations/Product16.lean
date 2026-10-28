module

public import Theory.SpecificGroups.Lyons.Atlas111WordRelations.Data

/-!
# Certified Lyons multiplication: w33 times w33

These 111 row checks certify `w33Matrix * w33Matrix = w66Matrix`.
The carry-free arithmetic soundness theorem gives the matrix identity.
Source: `../Atlas111Source/` and `../Atlas111WordSource/Generate.py`.
All closed certificates are checked by the Lean kernel.
-/

namespace Lyons.Atlas111WordCertificate

set_option Elab.async false

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w66_row0 :
    digitsEq 111 (rowProduct (w33Rows 0) w33Rows 111) (w66Rows 0)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w66_row1 :
    digitsEq 111 (rowProduct (w33Rows 1) w33Rows 111) (w66Rows 1)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w66_row2 :
    digitsEq 111 (rowProduct (w33Rows 2) w33Rows 111) (w66Rows 2)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w66_row3 :
    digitsEq 111 (rowProduct (w33Rows 3) w33Rows 111) (w66Rows 3)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w66_row4 :
    digitsEq 111 (rowProduct (w33Rows 4) w33Rows 111) (w66Rows 4)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w66_row5 :
    digitsEq 111 (rowProduct (w33Rows 5) w33Rows 111) (w66Rows 5)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w66_row6 :
    digitsEq 111 (rowProduct (w33Rows 6) w33Rows 111) (w66Rows 6)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w66_row7 :
    digitsEq 111 (rowProduct (w33Rows 7) w33Rows 111) (w66Rows 7)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w66_row8 :
    digitsEq 111 (rowProduct (w33Rows 8) w33Rows 111) (w66Rows 8)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w66_row9 :
    digitsEq 111 (rowProduct (w33Rows 9) w33Rows 111) (w66Rows 9)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w66_row10 :
    digitsEq 111 (rowProduct (w33Rows 10) w33Rows 111) (w66Rows 10)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w66_row11 :
    digitsEq 111 (rowProduct (w33Rows 11) w33Rows 111) (w66Rows 11)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w66_row12 :
    digitsEq 111 (rowProduct (w33Rows 12) w33Rows 111) (w66Rows 12)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w66_row13 :
    digitsEq 111 (rowProduct (w33Rows 13) w33Rows 111) (w66Rows 13)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w66_row14 :
    digitsEq 111 (rowProduct (w33Rows 14) w33Rows 111) (w66Rows 14)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w66_row15 :
    digitsEq 111 (rowProduct (w33Rows 15) w33Rows 111) (w66Rows 15)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w66_row16 :
    digitsEq 111 (rowProduct (w33Rows 16) w33Rows 111) (w66Rows 16)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w66_row17 :
    digitsEq 111 (rowProduct (w33Rows 17) w33Rows 111) (w66Rows 17)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w66_row18 :
    digitsEq 111 (rowProduct (w33Rows 18) w33Rows 111) (w66Rows 18)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w66_row19 :
    digitsEq 111 (rowProduct (w33Rows 19) w33Rows 111) (w66Rows 19)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w66_row20 :
    digitsEq 111 (rowProduct (w33Rows 20) w33Rows 111) (w66Rows 20)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w66_row21 :
    digitsEq 111 (rowProduct (w33Rows 21) w33Rows 111) (w66Rows 21)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w66_row22 :
    digitsEq 111 (rowProduct (w33Rows 22) w33Rows 111) (w66Rows 22)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w66_row23 :
    digitsEq 111 (rowProduct (w33Rows 23) w33Rows 111) (w66Rows 23)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w66_row24 :
    digitsEq 111 (rowProduct (w33Rows 24) w33Rows 111) (w66Rows 24)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w66_row25 :
    digitsEq 111 (rowProduct (w33Rows 25) w33Rows 111) (w66Rows 25)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w66_row26 :
    digitsEq 111 (rowProduct (w33Rows 26) w33Rows 111) (w66Rows 26)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w66_row27 :
    digitsEq 111 (rowProduct (w33Rows 27) w33Rows 111) (w66Rows 27)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w66_row28 :
    digitsEq 111 (rowProduct (w33Rows 28) w33Rows 111) (w66Rows 28)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w66_row29 :
    digitsEq 111 (rowProduct (w33Rows 29) w33Rows 111) (w66Rows 29)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w66_row30 :
    digitsEq 111 (rowProduct (w33Rows 30) w33Rows 111) (w66Rows 30)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w66_row31 :
    digitsEq 111 (rowProduct (w33Rows 31) w33Rows 111) (w66Rows 31)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w66_row32 :
    digitsEq 111 (rowProduct (w33Rows 32) w33Rows 111) (w66Rows 32)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w66_row33 :
    digitsEq 111 (rowProduct (w33Rows 33) w33Rows 111) (w66Rows 33)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w66_row34 :
    digitsEq 111 (rowProduct (w33Rows 34) w33Rows 111) (w66Rows 34)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w66_row35 :
    digitsEq 111 (rowProduct (w33Rows 35) w33Rows 111) (w66Rows 35)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w66_row36 :
    digitsEq 111 (rowProduct (w33Rows 36) w33Rows 111) (w66Rows 36)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w66_row37 :
    digitsEq 111 (rowProduct (w33Rows 37) w33Rows 111) (w66Rows 37)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w66_row38 :
    digitsEq 111 (rowProduct (w33Rows 38) w33Rows 111) (w66Rows 38)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w66_row39 :
    digitsEq 111 (rowProduct (w33Rows 39) w33Rows 111) (w66Rows 39)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w66_row40 :
    digitsEq 111 (rowProduct (w33Rows 40) w33Rows 111) (w66Rows 40)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w66_row41 :
    digitsEq 111 (rowProduct (w33Rows 41) w33Rows 111) (w66Rows 41)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w66_row42 :
    digitsEq 111 (rowProduct (w33Rows 42) w33Rows 111) (w66Rows 42)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w66_row43 :
    digitsEq 111 (rowProduct (w33Rows 43) w33Rows 111) (w66Rows 43)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w66_row44 :
    digitsEq 111 (rowProduct (w33Rows 44) w33Rows 111) (w66Rows 44)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w66_row45 :
    digitsEq 111 (rowProduct (w33Rows 45) w33Rows 111) (w66Rows 45)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w66_row46 :
    digitsEq 111 (rowProduct (w33Rows 46) w33Rows 111) (w66Rows 46)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w66_row47 :
    digitsEq 111 (rowProduct (w33Rows 47) w33Rows 111) (w66Rows 47)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w66_row48 :
    digitsEq 111 (rowProduct (w33Rows 48) w33Rows 111) (w66Rows 48)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w66_row49 :
    digitsEq 111 (rowProduct (w33Rows 49) w33Rows 111) (w66Rows 49)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w66_row50 :
    digitsEq 111 (rowProduct (w33Rows 50) w33Rows 111) (w66Rows 50)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w66_row51 :
    digitsEq 111 (rowProduct (w33Rows 51) w33Rows 111) (w66Rows 51)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w66_row52 :
    digitsEq 111 (rowProduct (w33Rows 52) w33Rows 111) (w66Rows 52)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w66_row53 :
    digitsEq 111 (rowProduct (w33Rows 53) w33Rows 111) (w66Rows 53)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w66_row54 :
    digitsEq 111 (rowProduct (w33Rows 54) w33Rows 111) (w66Rows 54)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w66_row55 :
    digitsEq 111 (rowProduct (w33Rows 55) w33Rows 111) (w66Rows 55)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w66_row56 :
    digitsEq 111 (rowProduct (w33Rows 56) w33Rows 111) (w66Rows 56)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w66_row57 :
    digitsEq 111 (rowProduct (w33Rows 57) w33Rows 111) (w66Rows 57)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w66_row58 :
    digitsEq 111 (rowProduct (w33Rows 58) w33Rows 111) (w66Rows 58)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w66_row59 :
    digitsEq 111 (rowProduct (w33Rows 59) w33Rows 111) (w66Rows 59)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w66_row60 :
    digitsEq 111 (rowProduct (w33Rows 60) w33Rows 111) (w66Rows 60)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w66_row61 :
    digitsEq 111 (rowProduct (w33Rows 61) w33Rows 111) (w66Rows 61)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w66_row62 :
    digitsEq 111 (rowProduct (w33Rows 62) w33Rows 111) (w66Rows 62)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w66_row63 :
    digitsEq 111 (rowProduct (w33Rows 63) w33Rows 111) (w66Rows 63)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w66_row64 :
    digitsEq 111 (rowProduct (w33Rows 64) w33Rows 111) (w66Rows 64)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w66_row65 :
    digitsEq 111 (rowProduct (w33Rows 65) w33Rows 111) (w66Rows 65)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w66_row66 :
    digitsEq 111 (rowProduct (w33Rows 66) w33Rows 111) (w66Rows 66)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w66_row67 :
    digitsEq 111 (rowProduct (w33Rows 67) w33Rows 111) (w66Rows 67)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w66_row68 :
    digitsEq 111 (rowProduct (w33Rows 68) w33Rows 111) (w66Rows 68)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w66_row69 :
    digitsEq 111 (rowProduct (w33Rows 69) w33Rows 111) (w66Rows 69)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w66_row70 :
    digitsEq 111 (rowProduct (w33Rows 70) w33Rows 111) (w66Rows 70)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w66_row71 :
    digitsEq 111 (rowProduct (w33Rows 71) w33Rows 111) (w66Rows 71)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w66_row72 :
    digitsEq 111 (rowProduct (w33Rows 72) w33Rows 111) (w66Rows 72)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w66_row73 :
    digitsEq 111 (rowProduct (w33Rows 73) w33Rows 111) (w66Rows 73)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w66_row74 :
    digitsEq 111 (rowProduct (w33Rows 74) w33Rows 111) (w66Rows 74)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w66_row75 :
    digitsEq 111 (rowProduct (w33Rows 75) w33Rows 111) (w66Rows 75)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w66_row76 :
    digitsEq 111 (rowProduct (w33Rows 76) w33Rows 111) (w66Rows 76)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w66_row77 :
    digitsEq 111 (rowProduct (w33Rows 77) w33Rows 111) (w66Rows 77)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w66_row78 :
    digitsEq 111 (rowProduct (w33Rows 78) w33Rows 111) (w66Rows 78)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w66_row79 :
    digitsEq 111 (rowProduct (w33Rows 79) w33Rows 111) (w66Rows 79)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w66_row80 :
    digitsEq 111 (rowProduct (w33Rows 80) w33Rows 111) (w66Rows 80)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w66_row81 :
    digitsEq 111 (rowProduct (w33Rows 81) w33Rows 111) (w66Rows 81)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w66_row82 :
    digitsEq 111 (rowProduct (w33Rows 82) w33Rows 111) (w66Rows 82)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w66_row83 :
    digitsEq 111 (rowProduct (w33Rows 83) w33Rows 111) (w66Rows 83)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w66_row84 :
    digitsEq 111 (rowProduct (w33Rows 84) w33Rows 111) (w66Rows 84)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w66_row85 :
    digitsEq 111 (rowProduct (w33Rows 85) w33Rows 111) (w66Rows 85)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w66_row86 :
    digitsEq 111 (rowProduct (w33Rows 86) w33Rows 111) (w66Rows 86)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w66_row87 :
    digitsEq 111 (rowProduct (w33Rows 87) w33Rows 111) (w66Rows 87)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w66_row88 :
    digitsEq 111 (rowProduct (w33Rows 88) w33Rows 111) (w66Rows 88)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w66_row89 :
    digitsEq 111 (rowProduct (w33Rows 89) w33Rows 111) (w66Rows 89)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w66_row90 :
    digitsEq 111 (rowProduct (w33Rows 90) w33Rows 111) (w66Rows 90)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w66_row91 :
    digitsEq 111 (rowProduct (w33Rows 91) w33Rows 111) (w66Rows 91)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w66_row92 :
    digitsEq 111 (rowProduct (w33Rows 92) w33Rows 111) (w66Rows 92)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w66_row93 :
    digitsEq 111 (rowProduct (w33Rows 93) w33Rows 111) (w66Rows 93)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w66_row94 :
    digitsEq 111 (rowProduct (w33Rows 94) w33Rows 111) (w66Rows 94)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w66_row95 :
    digitsEq 111 (rowProduct (w33Rows 95) w33Rows 111) (w66Rows 95)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w66_row96 :
    digitsEq 111 (rowProduct (w33Rows 96) w33Rows 111) (w66Rows 96)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w66_row97 :
    digitsEq 111 (rowProduct (w33Rows 97) w33Rows 111) (w66Rows 97)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w66_row98 :
    digitsEq 111 (rowProduct (w33Rows 98) w33Rows 111) (w66Rows 98)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w66_row99 :
    digitsEq 111 (rowProduct (w33Rows 99) w33Rows 111) (w66Rows 99)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w66_row100 :
    digitsEq 111 (rowProduct (w33Rows 100) w33Rows 111) (w66Rows 100)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w66_row101 :
    digitsEq 111 (rowProduct (w33Rows 101) w33Rows 111) (w66Rows 101)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w66_row102 :
    digitsEq 111 (rowProduct (w33Rows 102) w33Rows 111) (w66Rows 102)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w66_row103 :
    digitsEq 111 (rowProduct (w33Rows 103) w33Rows 111) (w66Rows 103)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w66_row104 :
    digitsEq 111 (rowProduct (w33Rows 104) w33Rows 111) (w66Rows 104)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w66_row105 :
    digitsEq 111 (rowProduct (w33Rows 105) w33Rows 111) (w66Rows 105)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w66_row106 :
    digitsEq 111 (rowProduct (w33Rows 106) w33Rows 111) (w66Rows 106)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w66_row107 :
    digitsEq 111 (rowProduct (w33Rows 107) w33Rows 111) (w66Rows 107)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w66_row108 :
    digitsEq 111 (rowProduct (w33Rows 108) w33Rows 111) (w66Rows 108)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w66_row109 :
    digitsEq 111 (rowProduct (w33Rows 109) w33Rows 111) (w66Rows 109)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w66_row110 :
    digitsEq 111 (rowProduct (w33Rows 110) w33Rows 111) (w66Rows 110)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem w66_rows : ∀ i,
    digitsEq 111 (rowProduct (w33Rows i) w33Rows 111) (w66Rows i) = true :=
  (Fin.cases w66_row0
    (Fin.cases w66_row1
    (Fin.cases w66_row2
    (Fin.cases w66_row3
    (Fin.cases w66_row4
    (Fin.cases w66_row5
    (Fin.cases w66_row6
    (Fin.cases w66_row7
    (Fin.cases w66_row8
    (Fin.cases w66_row9
    (Fin.cases w66_row10
    (Fin.cases w66_row11
    (Fin.cases w66_row12
    (Fin.cases w66_row13
    (Fin.cases w66_row14
    (Fin.cases w66_row15
    (Fin.cases w66_row16
    (Fin.cases w66_row17
    (Fin.cases w66_row18
    (Fin.cases w66_row19
    (Fin.cases w66_row20
    (Fin.cases w66_row21
    (Fin.cases w66_row22
    (Fin.cases w66_row23
    (Fin.cases w66_row24
    (Fin.cases w66_row25
    (Fin.cases w66_row26
    (Fin.cases w66_row27
    (Fin.cases w66_row28
    (Fin.cases w66_row29
    (Fin.cases w66_row30
    (Fin.cases w66_row31
    (Fin.cases w66_row32
    (Fin.cases w66_row33
    (Fin.cases w66_row34
    (Fin.cases w66_row35
    (Fin.cases w66_row36
    (Fin.cases w66_row37
    (Fin.cases w66_row38
    (Fin.cases w66_row39
    (Fin.cases w66_row40
    (Fin.cases w66_row41
    (Fin.cases w66_row42
    (Fin.cases w66_row43
    (Fin.cases w66_row44
    (Fin.cases w66_row45
    (Fin.cases w66_row46
    (Fin.cases w66_row47
    (Fin.cases w66_row48
    (Fin.cases w66_row49
    (Fin.cases w66_row50
    (Fin.cases w66_row51
    (Fin.cases w66_row52
    (Fin.cases w66_row53
    (Fin.cases w66_row54
    (Fin.cases w66_row55
    (Fin.cases w66_row56
    (Fin.cases w66_row57
    (Fin.cases w66_row58
    (Fin.cases w66_row59
    (Fin.cases w66_row60
    (Fin.cases w66_row61
    (Fin.cases w66_row62
    (Fin.cases w66_row63
    (Fin.cases w66_row64
    (Fin.cases w66_row65
    (Fin.cases w66_row66
    (Fin.cases w66_row67
    (Fin.cases w66_row68
    (Fin.cases w66_row69
    (Fin.cases w66_row70
    (Fin.cases w66_row71
    (Fin.cases w66_row72
    (Fin.cases w66_row73
    (Fin.cases w66_row74
    (Fin.cases w66_row75
    (Fin.cases w66_row76
    (Fin.cases w66_row77
    (Fin.cases w66_row78
    (Fin.cases w66_row79
    (Fin.cases w66_row80
    (Fin.cases w66_row81
    (Fin.cases w66_row82
    (Fin.cases w66_row83
    (Fin.cases w66_row84
    (Fin.cases w66_row85
    (Fin.cases w66_row86
    (Fin.cases w66_row87
    (Fin.cases w66_row88
    (Fin.cases w66_row89
    (Fin.cases w66_row90
    (Fin.cases w66_row91
    (Fin.cases w66_row92
    (Fin.cases w66_row93
    (Fin.cases w66_row94
    (Fin.cases w66_row95
    (Fin.cases w66_row96
    (Fin.cases w66_row97
    (Fin.cases w66_row98
    (Fin.cases w66_row99
    (Fin.cases w66_row100
    (Fin.cases w66_row101
    (Fin.cases w66_row102
    (Fin.cases w66_row103
    (Fin.cases w66_row104
    (Fin.cases w66_row105
    (Fin.cases w66_row106
    (Fin.cases w66_row107
    (Fin.cases w66_row108
    (Fin.cases w66_row109
    (Fin.cases w66_row110
    (fun i => Fin.elim0 i))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

/-- Checked multiplication in the actual matrix algebra. -/
public theorem mul_w66 : w33Matrix * w33Matrix = w66Matrix :=
  decode_mul _ _ _ w33_small w33_small w66_rows

end Lyons.Atlas111WordCertificate
