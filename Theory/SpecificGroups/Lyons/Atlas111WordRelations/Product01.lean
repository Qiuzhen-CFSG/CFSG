module

public import Theory.SpecificGroups.Lyons.Atlas111WordRelations.Data

/-!
# Certified Lyons multiplication: b2 times b2

These 111 row checks certify `b2Matrix * b2Matrix = b4Matrix`.
The carry-free arithmetic soundness theorem gives the matrix identity.
Source: `../Atlas111Source/` and `../Atlas111WordSource/Generate.py`.
All closed certificates are checked by the Lean kernel.
-/

namespace Lyons.Atlas111WordCertificate

set_option Elab.async false

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem b4_row0 :
    digitsEq 111 (rowProduct (b2Rows 0) b2Rows 111) (b4Rows 0)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem b4_row1 :
    digitsEq 111 (rowProduct (b2Rows 1) b2Rows 111) (b4Rows 1)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem b4_row2 :
    digitsEq 111 (rowProduct (b2Rows 2) b2Rows 111) (b4Rows 2)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem b4_row3 :
    digitsEq 111 (rowProduct (b2Rows 3) b2Rows 111) (b4Rows 3)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem b4_row4 :
    digitsEq 111 (rowProduct (b2Rows 4) b2Rows 111) (b4Rows 4)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem b4_row5 :
    digitsEq 111 (rowProduct (b2Rows 5) b2Rows 111) (b4Rows 5)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem b4_row6 :
    digitsEq 111 (rowProduct (b2Rows 6) b2Rows 111) (b4Rows 6)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem b4_row7 :
    digitsEq 111 (rowProduct (b2Rows 7) b2Rows 111) (b4Rows 7)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem b4_row8 :
    digitsEq 111 (rowProduct (b2Rows 8) b2Rows 111) (b4Rows 8)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem b4_row9 :
    digitsEq 111 (rowProduct (b2Rows 9) b2Rows 111) (b4Rows 9)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem b4_row10 :
    digitsEq 111 (rowProduct (b2Rows 10) b2Rows 111) (b4Rows 10)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem b4_row11 :
    digitsEq 111 (rowProduct (b2Rows 11) b2Rows 111) (b4Rows 11)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem b4_row12 :
    digitsEq 111 (rowProduct (b2Rows 12) b2Rows 111) (b4Rows 12)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem b4_row13 :
    digitsEq 111 (rowProduct (b2Rows 13) b2Rows 111) (b4Rows 13)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem b4_row14 :
    digitsEq 111 (rowProduct (b2Rows 14) b2Rows 111) (b4Rows 14)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem b4_row15 :
    digitsEq 111 (rowProduct (b2Rows 15) b2Rows 111) (b4Rows 15)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem b4_row16 :
    digitsEq 111 (rowProduct (b2Rows 16) b2Rows 111) (b4Rows 16)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem b4_row17 :
    digitsEq 111 (rowProduct (b2Rows 17) b2Rows 111) (b4Rows 17)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem b4_row18 :
    digitsEq 111 (rowProduct (b2Rows 18) b2Rows 111) (b4Rows 18)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem b4_row19 :
    digitsEq 111 (rowProduct (b2Rows 19) b2Rows 111) (b4Rows 19)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem b4_row20 :
    digitsEq 111 (rowProduct (b2Rows 20) b2Rows 111) (b4Rows 20)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem b4_row21 :
    digitsEq 111 (rowProduct (b2Rows 21) b2Rows 111) (b4Rows 21)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem b4_row22 :
    digitsEq 111 (rowProduct (b2Rows 22) b2Rows 111) (b4Rows 22)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem b4_row23 :
    digitsEq 111 (rowProduct (b2Rows 23) b2Rows 111) (b4Rows 23)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem b4_row24 :
    digitsEq 111 (rowProduct (b2Rows 24) b2Rows 111) (b4Rows 24)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem b4_row25 :
    digitsEq 111 (rowProduct (b2Rows 25) b2Rows 111) (b4Rows 25)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem b4_row26 :
    digitsEq 111 (rowProduct (b2Rows 26) b2Rows 111) (b4Rows 26)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem b4_row27 :
    digitsEq 111 (rowProduct (b2Rows 27) b2Rows 111) (b4Rows 27)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem b4_row28 :
    digitsEq 111 (rowProduct (b2Rows 28) b2Rows 111) (b4Rows 28)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem b4_row29 :
    digitsEq 111 (rowProduct (b2Rows 29) b2Rows 111) (b4Rows 29)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem b4_row30 :
    digitsEq 111 (rowProduct (b2Rows 30) b2Rows 111) (b4Rows 30)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem b4_row31 :
    digitsEq 111 (rowProduct (b2Rows 31) b2Rows 111) (b4Rows 31)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem b4_row32 :
    digitsEq 111 (rowProduct (b2Rows 32) b2Rows 111) (b4Rows 32)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem b4_row33 :
    digitsEq 111 (rowProduct (b2Rows 33) b2Rows 111) (b4Rows 33)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem b4_row34 :
    digitsEq 111 (rowProduct (b2Rows 34) b2Rows 111) (b4Rows 34)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem b4_row35 :
    digitsEq 111 (rowProduct (b2Rows 35) b2Rows 111) (b4Rows 35)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem b4_row36 :
    digitsEq 111 (rowProduct (b2Rows 36) b2Rows 111) (b4Rows 36)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem b4_row37 :
    digitsEq 111 (rowProduct (b2Rows 37) b2Rows 111) (b4Rows 37)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem b4_row38 :
    digitsEq 111 (rowProduct (b2Rows 38) b2Rows 111) (b4Rows 38)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem b4_row39 :
    digitsEq 111 (rowProduct (b2Rows 39) b2Rows 111) (b4Rows 39)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem b4_row40 :
    digitsEq 111 (rowProduct (b2Rows 40) b2Rows 111) (b4Rows 40)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem b4_row41 :
    digitsEq 111 (rowProduct (b2Rows 41) b2Rows 111) (b4Rows 41)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem b4_row42 :
    digitsEq 111 (rowProduct (b2Rows 42) b2Rows 111) (b4Rows 42)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem b4_row43 :
    digitsEq 111 (rowProduct (b2Rows 43) b2Rows 111) (b4Rows 43)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem b4_row44 :
    digitsEq 111 (rowProduct (b2Rows 44) b2Rows 111) (b4Rows 44)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem b4_row45 :
    digitsEq 111 (rowProduct (b2Rows 45) b2Rows 111) (b4Rows 45)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem b4_row46 :
    digitsEq 111 (rowProduct (b2Rows 46) b2Rows 111) (b4Rows 46)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem b4_row47 :
    digitsEq 111 (rowProduct (b2Rows 47) b2Rows 111) (b4Rows 47)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem b4_row48 :
    digitsEq 111 (rowProduct (b2Rows 48) b2Rows 111) (b4Rows 48)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem b4_row49 :
    digitsEq 111 (rowProduct (b2Rows 49) b2Rows 111) (b4Rows 49)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem b4_row50 :
    digitsEq 111 (rowProduct (b2Rows 50) b2Rows 111) (b4Rows 50)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem b4_row51 :
    digitsEq 111 (rowProduct (b2Rows 51) b2Rows 111) (b4Rows 51)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem b4_row52 :
    digitsEq 111 (rowProduct (b2Rows 52) b2Rows 111) (b4Rows 52)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem b4_row53 :
    digitsEq 111 (rowProduct (b2Rows 53) b2Rows 111) (b4Rows 53)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem b4_row54 :
    digitsEq 111 (rowProduct (b2Rows 54) b2Rows 111) (b4Rows 54)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem b4_row55 :
    digitsEq 111 (rowProduct (b2Rows 55) b2Rows 111) (b4Rows 55)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem b4_row56 :
    digitsEq 111 (rowProduct (b2Rows 56) b2Rows 111) (b4Rows 56)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem b4_row57 :
    digitsEq 111 (rowProduct (b2Rows 57) b2Rows 111) (b4Rows 57)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem b4_row58 :
    digitsEq 111 (rowProduct (b2Rows 58) b2Rows 111) (b4Rows 58)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem b4_row59 :
    digitsEq 111 (rowProduct (b2Rows 59) b2Rows 111) (b4Rows 59)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem b4_row60 :
    digitsEq 111 (rowProduct (b2Rows 60) b2Rows 111) (b4Rows 60)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem b4_row61 :
    digitsEq 111 (rowProduct (b2Rows 61) b2Rows 111) (b4Rows 61)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem b4_row62 :
    digitsEq 111 (rowProduct (b2Rows 62) b2Rows 111) (b4Rows 62)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem b4_row63 :
    digitsEq 111 (rowProduct (b2Rows 63) b2Rows 111) (b4Rows 63)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem b4_row64 :
    digitsEq 111 (rowProduct (b2Rows 64) b2Rows 111) (b4Rows 64)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem b4_row65 :
    digitsEq 111 (rowProduct (b2Rows 65) b2Rows 111) (b4Rows 65)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem b4_row66 :
    digitsEq 111 (rowProduct (b2Rows 66) b2Rows 111) (b4Rows 66)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem b4_row67 :
    digitsEq 111 (rowProduct (b2Rows 67) b2Rows 111) (b4Rows 67)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem b4_row68 :
    digitsEq 111 (rowProduct (b2Rows 68) b2Rows 111) (b4Rows 68)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem b4_row69 :
    digitsEq 111 (rowProduct (b2Rows 69) b2Rows 111) (b4Rows 69)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem b4_row70 :
    digitsEq 111 (rowProduct (b2Rows 70) b2Rows 111) (b4Rows 70)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem b4_row71 :
    digitsEq 111 (rowProduct (b2Rows 71) b2Rows 111) (b4Rows 71)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem b4_row72 :
    digitsEq 111 (rowProduct (b2Rows 72) b2Rows 111) (b4Rows 72)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem b4_row73 :
    digitsEq 111 (rowProduct (b2Rows 73) b2Rows 111) (b4Rows 73)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem b4_row74 :
    digitsEq 111 (rowProduct (b2Rows 74) b2Rows 111) (b4Rows 74)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem b4_row75 :
    digitsEq 111 (rowProduct (b2Rows 75) b2Rows 111) (b4Rows 75)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem b4_row76 :
    digitsEq 111 (rowProduct (b2Rows 76) b2Rows 111) (b4Rows 76)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem b4_row77 :
    digitsEq 111 (rowProduct (b2Rows 77) b2Rows 111) (b4Rows 77)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem b4_row78 :
    digitsEq 111 (rowProduct (b2Rows 78) b2Rows 111) (b4Rows 78)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem b4_row79 :
    digitsEq 111 (rowProduct (b2Rows 79) b2Rows 111) (b4Rows 79)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem b4_row80 :
    digitsEq 111 (rowProduct (b2Rows 80) b2Rows 111) (b4Rows 80)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem b4_row81 :
    digitsEq 111 (rowProduct (b2Rows 81) b2Rows 111) (b4Rows 81)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem b4_row82 :
    digitsEq 111 (rowProduct (b2Rows 82) b2Rows 111) (b4Rows 82)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem b4_row83 :
    digitsEq 111 (rowProduct (b2Rows 83) b2Rows 111) (b4Rows 83)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem b4_row84 :
    digitsEq 111 (rowProduct (b2Rows 84) b2Rows 111) (b4Rows 84)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem b4_row85 :
    digitsEq 111 (rowProduct (b2Rows 85) b2Rows 111) (b4Rows 85)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem b4_row86 :
    digitsEq 111 (rowProduct (b2Rows 86) b2Rows 111) (b4Rows 86)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem b4_row87 :
    digitsEq 111 (rowProduct (b2Rows 87) b2Rows 111) (b4Rows 87)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem b4_row88 :
    digitsEq 111 (rowProduct (b2Rows 88) b2Rows 111) (b4Rows 88)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem b4_row89 :
    digitsEq 111 (rowProduct (b2Rows 89) b2Rows 111) (b4Rows 89)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem b4_row90 :
    digitsEq 111 (rowProduct (b2Rows 90) b2Rows 111) (b4Rows 90)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem b4_row91 :
    digitsEq 111 (rowProduct (b2Rows 91) b2Rows 111) (b4Rows 91)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem b4_row92 :
    digitsEq 111 (rowProduct (b2Rows 92) b2Rows 111) (b4Rows 92)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem b4_row93 :
    digitsEq 111 (rowProduct (b2Rows 93) b2Rows 111) (b4Rows 93)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem b4_row94 :
    digitsEq 111 (rowProduct (b2Rows 94) b2Rows 111) (b4Rows 94)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem b4_row95 :
    digitsEq 111 (rowProduct (b2Rows 95) b2Rows 111) (b4Rows 95)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem b4_row96 :
    digitsEq 111 (rowProduct (b2Rows 96) b2Rows 111) (b4Rows 96)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem b4_row97 :
    digitsEq 111 (rowProduct (b2Rows 97) b2Rows 111) (b4Rows 97)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem b4_row98 :
    digitsEq 111 (rowProduct (b2Rows 98) b2Rows 111) (b4Rows 98)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem b4_row99 :
    digitsEq 111 (rowProduct (b2Rows 99) b2Rows 111) (b4Rows 99)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem b4_row100 :
    digitsEq 111 (rowProduct (b2Rows 100) b2Rows 111) (b4Rows 100)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem b4_row101 :
    digitsEq 111 (rowProduct (b2Rows 101) b2Rows 111) (b4Rows 101)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem b4_row102 :
    digitsEq 111 (rowProduct (b2Rows 102) b2Rows 111) (b4Rows 102)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem b4_row103 :
    digitsEq 111 (rowProduct (b2Rows 103) b2Rows 111) (b4Rows 103)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem b4_row104 :
    digitsEq 111 (rowProduct (b2Rows 104) b2Rows 111) (b4Rows 104)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem b4_row105 :
    digitsEq 111 (rowProduct (b2Rows 105) b2Rows 111) (b4Rows 105)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem b4_row106 :
    digitsEq 111 (rowProduct (b2Rows 106) b2Rows 111) (b4Rows 106)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem b4_row107 :
    digitsEq 111 (rowProduct (b2Rows 107) b2Rows 111) (b4Rows 107)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem b4_row108 :
    digitsEq 111 (rowProduct (b2Rows 108) b2Rows 111) (b4Rows 108)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem b4_row109 :
    digitsEq 111 (rowProduct (b2Rows 109) b2Rows 111) (b4Rows 109)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem b4_row110 :
    digitsEq 111 (rowProduct (b2Rows 110) b2Rows 111) (b4Rows 110)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem b4_rows : ∀ i,
    digitsEq 111 (rowProduct (b2Rows i) b2Rows 111) (b4Rows i) = true :=
  (Fin.cases b4_row0
    (Fin.cases b4_row1
    (Fin.cases b4_row2
    (Fin.cases b4_row3
    (Fin.cases b4_row4
    (Fin.cases b4_row5
    (Fin.cases b4_row6
    (Fin.cases b4_row7
    (Fin.cases b4_row8
    (Fin.cases b4_row9
    (Fin.cases b4_row10
    (Fin.cases b4_row11
    (Fin.cases b4_row12
    (Fin.cases b4_row13
    (Fin.cases b4_row14
    (Fin.cases b4_row15
    (Fin.cases b4_row16
    (Fin.cases b4_row17
    (Fin.cases b4_row18
    (Fin.cases b4_row19
    (Fin.cases b4_row20
    (Fin.cases b4_row21
    (Fin.cases b4_row22
    (Fin.cases b4_row23
    (Fin.cases b4_row24
    (Fin.cases b4_row25
    (Fin.cases b4_row26
    (Fin.cases b4_row27
    (Fin.cases b4_row28
    (Fin.cases b4_row29
    (Fin.cases b4_row30
    (Fin.cases b4_row31
    (Fin.cases b4_row32
    (Fin.cases b4_row33
    (Fin.cases b4_row34
    (Fin.cases b4_row35
    (Fin.cases b4_row36
    (Fin.cases b4_row37
    (Fin.cases b4_row38
    (Fin.cases b4_row39
    (Fin.cases b4_row40
    (Fin.cases b4_row41
    (Fin.cases b4_row42
    (Fin.cases b4_row43
    (Fin.cases b4_row44
    (Fin.cases b4_row45
    (Fin.cases b4_row46
    (Fin.cases b4_row47
    (Fin.cases b4_row48
    (Fin.cases b4_row49
    (Fin.cases b4_row50
    (Fin.cases b4_row51
    (Fin.cases b4_row52
    (Fin.cases b4_row53
    (Fin.cases b4_row54
    (Fin.cases b4_row55
    (Fin.cases b4_row56
    (Fin.cases b4_row57
    (Fin.cases b4_row58
    (Fin.cases b4_row59
    (Fin.cases b4_row60
    (Fin.cases b4_row61
    (Fin.cases b4_row62
    (Fin.cases b4_row63
    (Fin.cases b4_row64
    (Fin.cases b4_row65
    (Fin.cases b4_row66
    (Fin.cases b4_row67
    (Fin.cases b4_row68
    (Fin.cases b4_row69
    (Fin.cases b4_row70
    (Fin.cases b4_row71
    (Fin.cases b4_row72
    (Fin.cases b4_row73
    (Fin.cases b4_row74
    (Fin.cases b4_row75
    (Fin.cases b4_row76
    (Fin.cases b4_row77
    (Fin.cases b4_row78
    (Fin.cases b4_row79
    (Fin.cases b4_row80
    (Fin.cases b4_row81
    (Fin.cases b4_row82
    (Fin.cases b4_row83
    (Fin.cases b4_row84
    (Fin.cases b4_row85
    (Fin.cases b4_row86
    (Fin.cases b4_row87
    (Fin.cases b4_row88
    (Fin.cases b4_row89
    (Fin.cases b4_row90
    (Fin.cases b4_row91
    (Fin.cases b4_row92
    (Fin.cases b4_row93
    (Fin.cases b4_row94
    (Fin.cases b4_row95
    (Fin.cases b4_row96
    (Fin.cases b4_row97
    (Fin.cases b4_row98
    (Fin.cases b4_row99
    (Fin.cases b4_row100
    (Fin.cases b4_row101
    (Fin.cases b4_row102
    (Fin.cases b4_row103
    (Fin.cases b4_row104
    (Fin.cases b4_row105
    (Fin.cases b4_row106
    (Fin.cases b4_row107
    (Fin.cases b4_row108
    (Fin.cases b4_row109
    (Fin.cases b4_row110
    (fun i => Fin.elim0 i))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

/-- Checked multiplication in the actual matrix algebra. -/
public theorem mul_b4 : b2Matrix * b2Matrix = b4Matrix :=
  decode_mul _ _ _ b2_small b2_small b4_rows

end Lyons.Atlas111WordCertificate
