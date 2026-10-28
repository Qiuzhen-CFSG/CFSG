module

public import Theory.SpecificGroups.Lyons.Atlas111WordRelations.Data

/-!
# Certified Lyons multiplication: ab2 times ab

These 111 row checks certify `ab2Matrix * abMatrix = ab3Matrix`.
The carry-free arithmetic soundness theorem gives the matrix identity.
Source: `../Atlas111Source/` and `../Atlas111WordSource/Generate.py`.
All closed certificates are checked by the Lean kernel.
-/

namespace Lyons.Atlas111WordCertificate

set_option Elab.async false

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem ab3_row0 :
    digitsEq 111 (rowProduct (ab2Rows 0) abRows 111) (ab3Rows 0)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem ab3_row1 :
    digitsEq 111 (rowProduct (ab2Rows 1) abRows 111) (ab3Rows 1)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem ab3_row2 :
    digitsEq 111 (rowProduct (ab2Rows 2) abRows 111) (ab3Rows 2)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem ab3_row3 :
    digitsEq 111 (rowProduct (ab2Rows 3) abRows 111) (ab3Rows 3)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem ab3_row4 :
    digitsEq 111 (rowProduct (ab2Rows 4) abRows 111) (ab3Rows 4)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem ab3_row5 :
    digitsEq 111 (rowProduct (ab2Rows 5) abRows 111) (ab3Rows 5)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem ab3_row6 :
    digitsEq 111 (rowProduct (ab2Rows 6) abRows 111) (ab3Rows 6)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem ab3_row7 :
    digitsEq 111 (rowProduct (ab2Rows 7) abRows 111) (ab3Rows 7)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem ab3_row8 :
    digitsEq 111 (rowProduct (ab2Rows 8) abRows 111) (ab3Rows 8)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem ab3_row9 :
    digitsEq 111 (rowProduct (ab2Rows 9) abRows 111) (ab3Rows 9)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem ab3_row10 :
    digitsEq 111 (rowProduct (ab2Rows 10) abRows 111) (ab3Rows 10)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem ab3_row11 :
    digitsEq 111 (rowProduct (ab2Rows 11) abRows 111) (ab3Rows 11)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem ab3_row12 :
    digitsEq 111 (rowProduct (ab2Rows 12) abRows 111) (ab3Rows 12)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem ab3_row13 :
    digitsEq 111 (rowProduct (ab2Rows 13) abRows 111) (ab3Rows 13)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem ab3_row14 :
    digitsEq 111 (rowProduct (ab2Rows 14) abRows 111) (ab3Rows 14)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem ab3_row15 :
    digitsEq 111 (rowProduct (ab2Rows 15) abRows 111) (ab3Rows 15)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem ab3_row16 :
    digitsEq 111 (rowProduct (ab2Rows 16) abRows 111) (ab3Rows 16)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem ab3_row17 :
    digitsEq 111 (rowProduct (ab2Rows 17) abRows 111) (ab3Rows 17)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem ab3_row18 :
    digitsEq 111 (rowProduct (ab2Rows 18) abRows 111) (ab3Rows 18)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem ab3_row19 :
    digitsEq 111 (rowProduct (ab2Rows 19) abRows 111) (ab3Rows 19)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem ab3_row20 :
    digitsEq 111 (rowProduct (ab2Rows 20) abRows 111) (ab3Rows 20)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem ab3_row21 :
    digitsEq 111 (rowProduct (ab2Rows 21) abRows 111) (ab3Rows 21)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem ab3_row22 :
    digitsEq 111 (rowProduct (ab2Rows 22) abRows 111) (ab3Rows 22)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem ab3_row23 :
    digitsEq 111 (rowProduct (ab2Rows 23) abRows 111) (ab3Rows 23)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem ab3_row24 :
    digitsEq 111 (rowProduct (ab2Rows 24) abRows 111) (ab3Rows 24)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem ab3_row25 :
    digitsEq 111 (rowProduct (ab2Rows 25) abRows 111) (ab3Rows 25)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem ab3_row26 :
    digitsEq 111 (rowProduct (ab2Rows 26) abRows 111) (ab3Rows 26)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem ab3_row27 :
    digitsEq 111 (rowProduct (ab2Rows 27) abRows 111) (ab3Rows 27)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem ab3_row28 :
    digitsEq 111 (rowProduct (ab2Rows 28) abRows 111) (ab3Rows 28)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem ab3_row29 :
    digitsEq 111 (rowProduct (ab2Rows 29) abRows 111) (ab3Rows 29)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem ab3_row30 :
    digitsEq 111 (rowProduct (ab2Rows 30) abRows 111) (ab3Rows 30)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem ab3_row31 :
    digitsEq 111 (rowProduct (ab2Rows 31) abRows 111) (ab3Rows 31)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem ab3_row32 :
    digitsEq 111 (rowProduct (ab2Rows 32) abRows 111) (ab3Rows 32)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem ab3_row33 :
    digitsEq 111 (rowProduct (ab2Rows 33) abRows 111) (ab3Rows 33)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem ab3_row34 :
    digitsEq 111 (rowProduct (ab2Rows 34) abRows 111) (ab3Rows 34)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem ab3_row35 :
    digitsEq 111 (rowProduct (ab2Rows 35) abRows 111) (ab3Rows 35)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem ab3_row36 :
    digitsEq 111 (rowProduct (ab2Rows 36) abRows 111) (ab3Rows 36)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem ab3_row37 :
    digitsEq 111 (rowProduct (ab2Rows 37) abRows 111) (ab3Rows 37)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem ab3_row38 :
    digitsEq 111 (rowProduct (ab2Rows 38) abRows 111) (ab3Rows 38)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem ab3_row39 :
    digitsEq 111 (rowProduct (ab2Rows 39) abRows 111) (ab3Rows 39)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem ab3_row40 :
    digitsEq 111 (rowProduct (ab2Rows 40) abRows 111) (ab3Rows 40)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem ab3_row41 :
    digitsEq 111 (rowProduct (ab2Rows 41) abRows 111) (ab3Rows 41)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem ab3_row42 :
    digitsEq 111 (rowProduct (ab2Rows 42) abRows 111) (ab3Rows 42)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem ab3_row43 :
    digitsEq 111 (rowProduct (ab2Rows 43) abRows 111) (ab3Rows 43)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem ab3_row44 :
    digitsEq 111 (rowProduct (ab2Rows 44) abRows 111) (ab3Rows 44)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem ab3_row45 :
    digitsEq 111 (rowProduct (ab2Rows 45) abRows 111) (ab3Rows 45)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem ab3_row46 :
    digitsEq 111 (rowProduct (ab2Rows 46) abRows 111) (ab3Rows 46)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem ab3_row47 :
    digitsEq 111 (rowProduct (ab2Rows 47) abRows 111) (ab3Rows 47)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem ab3_row48 :
    digitsEq 111 (rowProduct (ab2Rows 48) abRows 111) (ab3Rows 48)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem ab3_row49 :
    digitsEq 111 (rowProduct (ab2Rows 49) abRows 111) (ab3Rows 49)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem ab3_row50 :
    digitsEq 111 (rowProduct (ab2Rows 50) abRows 111) (ab3Rows 50)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem ab3_row51 :
    digitsEq 111 (rowProduct (ab2Rows 51) abRows 111) (ab3Rows 51)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem ab3_row52 :
    digitsEq 111 (rowProduct (ab2Rows 52) abRows 111) (ab3Rows 52)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem ab3_row53 :
    digitsEq 111 (rowProduct (ab2Rows 53) abRows 111) (ab3Rows 53)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem ab3_row54 :
    digitsEq 111 (rowProduct (ab2Rows 54) abRows 111) (ab3Rows 54)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem ab3_row55 :
    digitsEq 111 (rowProduct (ab2Rows 55) abRows 111) (ab3Rows 55)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem ab3_row56 :
    digitsEq 111 (rowProduct (ab2Rows 56) abRows 111) (ab3Rows 56)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem ab3_row57 :
    digitsEq 111 (rowProduct (ab2Rows 57) abRows 111) (ab3Rows 57)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem ab3_row58 :
    digitsEq 111 (rowProduct (ab2Rows 58) abRows 111) (ab3Rows 58)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem ab3_row59 :
    digitsEq 111 (rowProduct (ab2Rows 59) abRows 111) (ab3Rows 59)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem ab3_row60 :
    digitsEq 111 (rowProduct (ab2Rows 60) abRows 111) (ab3Rows 60)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem ab3_row61 :
    digitsEq 111 (rowProduct (ab2Rows 61) abRows 111) (ab3Rows 61)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem ab3_row62 :
    digitsEq 111 (rowProduct (ab2Rows 62) abRows 111) (ab3Rows 62)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem ab3_row63 :
    digitsEq 111 (rowProduct (ab2Rows 63) abRows 111) (ab3Rows 63)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem ab3_row64 :
    digitsEq 111 (rowProduct (ab2Rows 64) abRows 111) (ab3Rows 64)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem ab3_row65 :
    digitsEq 111 (rowProduct (ab2Rows 65) abRows 111) (ab3Rows 65)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem ab3_row66 :
    digitsEq 111 (rowProduct (ab2Rows 66) abRows 111) (ab3Rows 66)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem ab3_row67 :
    digitsEq 111 (rowProduct (ab2Rows 67) abRows 111) (ab3Rows 67)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem ab3_row68 :
    digitsEq 111 (rowProduct (ab2Rows 68) abRows 111) (ab3Rows 68)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem ab3_row69 :
    digitsEq 111 (rowProduct (ab2Rows 69) abRows 111) (ab3Rows 69)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem ab3_row70 :
    digitsEq 111 (rowProduct (ab2Rows 70) abRows 111) (ab3Rows 70)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem ab3_row71 :
    digitsEq 111 (rowProduct (ab2Rows 71) abRows 111) (ab3Rows 71)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem ab3_row72 :
    digitsEq 111 (rowProduct (ab2Rows 72) abRows 111) (ab3Rows 72)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem ab3_row73 :
    digitsEq 111 (rowProduct (ab2Rows 73) abRows 111) (ab3Rows 73)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem ab3_row74 :
    digitsEq 111 (rowProduct (ab2Rows 74) abRows 111) (ab3Rows 74)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem ab3_row75 :
    digitsEq 111 (rowProduct (ab2Rows 75) abRows 111) (ab3Rows 75)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem ab3_row76 :
    digitsEq 111 (rowProduct (ab2Rows 76) abRows 111) (ab3Rows 76)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem ab3_row77 :
    digitsEq 111 (rowProduct (ab2Rows 77) abRows 111) (ab3Rows 77)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem ab3_row78 :
    digitsEq 111 (rowProduct (ab2Rows 78) abRows 111) (ab3Rows 78)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem ab3_row79 :
    digitsEq 111 (rowProduct (ab2Rows 79) abRows 111) (ab3Rows 79)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem ab3_row80 :
    digitsEq 111 (rowProduct (ab2Rows 80) abRows 111) (ab3Rows 80)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem ab3_row81 :
    digitsEq 111 (rowProduct (ab2Rows 81) abRows 111) (ab3Rows 81)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem ab3_row82 :
    digitsEq 111 (rowProduct (ab2Rows 82) abRows 111) (ab3Rows 82)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem ab3_row83 :
    digitsEq 111 (rowProduct (ab2Rows 83) abRows 111) (ab3Rows 83)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem ab3_row84 :
    digitsEq 111 (rowProduct (ab2Rows 84) abRows 111) (ab3Rows 84)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem ab3_row85 :
    digitsEq 111 (rowProduct (ab2Rows 85) abRows 111) (ab3Rows 85)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem ab3_row86 :
    digitsEq 111 (rowProduct (ab2Rows 86) abRows 111) (ab3Rows 86)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem ab3_row87 :
    digitsEq 111 (rowProduct (ab2Rows 87) abRows 111) (ab3Rows 87)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem ab3_row88 :
    digitsEq 111 (rowProduct (ab2Rows 88) abRows 111) (ab3Rows 88)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem ab3_row89 :
    digitsEq 111 (rowProduct (ab2Rows 89) abRows 111) (ab3Rows 89)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem ab3_row90 :
    digitsEq 111 (rowProduct (ab2Rows 90) abRows 111) (ab3Rows 90)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem ab3_row91 :
    digitsEq 111 (rowProduct (ab2Rows 91) abRows 111) (ab3Rows 91)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem ab3_row92 :
    digitsEq 111 (rowProduct (ab2Rows 92) abRows 111) (ab3Rows 92)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem ab3_row93 :
    digitsEq 111 (rowProduct (ab2Rows 93) abRows 111) (ab3Rows 93)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem ab3_row94 :
    digitsEq 111 (rowProduct (ab2Rows 94) abRows 111) (ab3Rows 94)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem ab3_row95 :
    digitsEq 111 (rowProduct (ab2Rows 95) abRows 111) (ab3Rows 95)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem ab3_row96 :
    digitsEq 111 (rowProduct (ab2Rows 96) abRows 111) (ab3Rows 96)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem ab3_row97 :
    digitsEq 111 (rowProduct (ab2Rows 97) abRows 111) (ab3Rows 97)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem ab3_row98 :
    digitsEq 111 (rowProduct (ab2Rows 98) abRows 111) (ab3Rows 98)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem ab3_row99 :
    digitsEq 111 (rowProduct (ab2Rows 99) abRows 111) (ab3Rows 99)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem ab3_row100 :
    digitsEq 111 (rowProduct (ab2Rows 100) abRows 111) (ab3Rows 100)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem ab3_row101 :
    digitsEq 111 (rowProduct (ab2Rows 101) abRows 111) (ab3Rows 101)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem ab3_row102 :
    digitsEq 111 (rowProduct (ab2Rows 102) abRows 111) (ab3Rows 102)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem ab3_row103 :
    digitsEq 111 (rowProduct (ab2Rows 103) abRows 111) (ab3Rows 103)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem ab3_row104 :
    digitsEq 111 (rowProduct (ab2Rows 104) abRows 111) (ab3Rows 104)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem ab3_row105 :
    digitsEq 111 (rowProduct (ab2Rows 105) abRows 111) (ab3Rows 105)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem ab3_row106 :
    digitsEq 111 (rowProduct (ab2Rows 106) abRows 111) (ab3Rows 106)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem ab3_row107 :
    digitsEq 111 (rowProduct (ab2Rows 107) abRows 111) (ab3Rows 107)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem ab3_row108 :
    digitsEq 111 (rowProduct (ab2Rows 108) abRows 111) (ab3Rows 108)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem ab3_row109 :
    digitsEq 111 (rowProduct (ab2Rows 109) abRows 111) (ab3Rows 109)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem ab3_row110 :
    digitsEq 111 (rowProduct (ab2Rows 110) abRows 111) (ab3Rows 110)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem ab3_rows : ∀ i,
    digitsEq 111 (rowProduct (ab2Rows i) abRows 111) (ab3Rows i) = true :=
  (Fin.cases ab3_row0
    (Fin.cases ab3_row1
    (Fin.cases ab3_row2
    (Fin.cases ab3_row3
    (Fin.cases ab3_row4
    (Fin.cases ab3_row5
    (Fin.cases ab3_row6
    (Fin.cases ab3_row7
    (Fin.cases ab3_row8
    (Fin.cases ab3_row9
    (Fin.cases ab3_row10
    (Fin.cases ab3_row11
    (Fin.cases ab3_row12
    (Fin.cases ab3_row13
    (Fin.cases ab3_row14
    (Fin.cases ab3_row15
    (Fin.cases ab3_row16
    (Fin.cases ab3_row17
    (Fin.cases ab3_row18
    (Fin.cases ab3_row19
    (Fin.cases ab3_row20
    (Fin.cases ab3_row21
    (Fin.cases ab3_row22
    (Fin.cases ab3_row23
    (Fin.cases ab3_row24
    (Fin.cases ab3_row25
    (Fin.cases ab3_row26
    (Fin.cases ab3_row27
    (Fin.cases ab3_row28
    (Fin.cases ab3_row29
    (Fin.cases ab3_row30
    (Fin.cases ab3_row31
    (Fin.cases ab3_row32
    (Fin.cases ab3_row33
    (Fin.cases ab3_row34
    (Fin.cases ab3_row35
    (Fin.cases ab3_row36
    (Fin.cases ab3_row37
    (Fin.cases ab3_row38
    (Fin.cases ab3_row39
    (Fin.cases ab3_row40
    (Fin.cases ab3_row41
    (Fin.cases ab3_row42
    (Fin.cases ab3_row43
    (Fin.cases ab3_row44
    (Fin.cases ab3_row45
    (Fin.cases ab3_row46
    (Fin.cases ab3_row47
    (Fin.cases ab3_row48
    (Fin.cases ab3_row49
    (Fin.cases ab3_row50
    (Fin.cases ab3_row51
    (Fin.cases ab3_row52
    (Fin.cases ab3_row53
    (Fin.cases ab3_row54
    (Fin.cases ab3_row55
    (Fin.cases ab3_row56
    (Fin.cases ab3_row57
    (Fin.cases ab3_row58
    (Fin.cases ab3_row59
    (Fin.cases ab3_row60
    (Fin.cases ab3_row61
    (Fin.cases ab3_row62
    (Fin.cases ab3_row63
    (Fin.cases ab3_row64
    (Fin.cases ab3_row65
    (Fin.cases ab3_row66
    (Fin.cases ab3_row67
    (Fin.cases ab3_row68
    (Fin.cases ab3_row69
    (Fin.cases ab3_row70
    (Fin.cases ab3_row71
    (Fin.cases ab3_row72
    (Fin.cases ab3_row73
    (Fin.cases ab3_row74
    (Fin.cases ab3_row75
    (Fin.cases ab3_row76
    (Fin.cases ab3_row77
    (Fin.cases ab3_row78
    (Fin.cases ab3_row79
    (Fin.cases ab3_row80
    (Fin.cases ab3_row81
    (Fin.cases ab3_row82
    (Fin.cases ab3_row83
    (Fin.cases ab3_row84
    (Fin.cases ab3_row85
    (Fin.cases ab3_row86
    (Fin.cases ab3_row87
    (Fin.cases ab3_row88
    (Fin.cases ab3_row89
    (Fin.cases ab3_row90
    (Fin.cases ab3_row91
    (Fin.cases ab3_row92
    (Fin.cases ab3_row93
    (Fin.cases ab3_row94
    (Fin.cases ab3_row95
    (Fin.cases ab3_row96
    (Fin.cases ab3_row97
    (Fin.cases ab3_row98
    (Fin.cases ab3_row99
    (Fin.cases ab3_row100
    (Fin.cases ab3_row101
    (Fin.cases ab3_row102
    (Fin.cases ab3_row103
    (Fin.cases ab3_row104
    (Fin.cases ab3_row105
    (Fin.cases ab3_row106
    (Fin.cases ab3_row107
    (Fin.cases ab3_row108
    (Fin.cases ab3_row109
    (Fin.cases ab3_row110
    (fun i => Fin.elim0 i))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

/-- Checked multiplication in the actual matrix algebra. -/
public theorem mul_ab3 : ab2Matrix * abMatrix = ab3Matrix :=
  decode_mul _ _ _ ab2_small ab_small ab3_rows

end Lyons.Atlas111WordCertificate
