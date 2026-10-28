module

public import Theory.SpecificGroups.Lyons.Atlas111WordRelations.Data

/-!
# Certified Lyons multiplication: ab6 times ab

These 111 row checks certify `ab6Matrix * abMatrix = ab7Matrix`.
The carry-free arithmetic soundness theorem gives the matrix identity.
Source: `../Atlas111Source/` and `../Atlas111WordSource/Generate.py`.
All closed certificates are checked by the Lean kernel.
-/

namespace Lyons.Atlas111WordCertificate

set_option Elab.async false

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem ab7_row0 :
    digitsEq 111 (rowProduct (ab6Rows 0) abRows 111) (ab7Rows 0)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem ab7_row1 :
    digitsEq 111 (rowProduct (ab6Rows 1) abRows 111) (ab7Rows 1)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem ab7_row2 :
    digitsEq 111 (rowProduct (ab6Rows 2) abRows 111) (ab7Rows 2)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem ab7_row3 :
    digitsEq 111 (rowProduct (ab6Rows 3) abRows 111) (ab7Rows 3)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem ab7_row4 :
    digitsEq 111 (rowProduct (ab6Rows 4) abRows 111) (ab7Rows 4)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem ab7_row5 :
    digitsEq 111 (rowProduct (ab6Rows 5) abRows 111) (ab7Rows 5)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem ab7_row6 :
    digitsEq 111 (rowProduct (ab6Rows 6) abRows 111) (ab7Rows 6)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem ab7_row7 :
    digitsEq 111 (rowProduct (ab6Rows 7) abRows 111) (ab7Rows 7)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem ab7_row8 :
    digitsEq 111 (rowProduct (ab6Rows 8) abRows 111) (ab7Rows 8)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem ab7_row9 :
    digitsEq 111 (rowProduct (ab6Rows 9) abRows 111) (ab7Rows 9)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem ab7_row10 :
    digitsEq 111 (rowProduct (ab6Rows 10) abRows 111) (ab7Rows 10)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem ab7_row11 :
    digitsEq 111 (rowProduct (ab6Rows 11) abRows 111) (ab7Rows 11)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem ab7_row12 :
    digitsEq 111 (rowProduct (ab6Rows 12) abRows 111) (ab7Rows 12)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem ab7_row13 :
    digitsEq 111 (rowProduct (ab6Rows 13) abRows 111) (ab7Rows 13)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem ab7_row14 :
    digitsEq 111 (rowProduct (ab6Rows 14) abRows 111) (ab7Rows 14)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem ab7_row15 :
    digitsEq 111 (rowProduct (ab6Rows 15) abRows 111) (ab7Rows 15)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem ab7_row16 :
    digitsEq 111 (rowProduct (ab6Rows 16) abRows 111) (ab7Rows 16)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem ab7_row17 :
    digitsEq 111 (rowProduct (ab6Rows 17) abRows 111) (ab7Rows 17)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem ab7_row18 :
    digitsEq 111 (rowProduct (ab6Rows 18) abRows 111) (ab7Rows 18)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem ab7_row19 :
    digitsEq 111 (rowProduct (ab6Rows 19) abRows 111) (ab7Rows 19)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem ab7_row20 :
    digitsEq 111 (rowProduct (ab6Rows 20) abRows 111) (ab7Rows 20)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem ab7_row21 :
    digitsEq 111 (rowProduct (ab6Rows 21) abRows 111) (ab7Rows 21)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem ab7_row22 :
    digitsEq 111 (rowProduct (ab6Rows 22) abRows 111) (ab7Rows 22)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem ab7_row23 :
    digitsEq 111 (rowProduct (ab6Rows 23) abRows 111) (ab7Rows 23)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem ab7_row24 :
    digitsEq 111 (rowProduct (ab6Rows 24) abRows 111) (ab7Rows 24)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem ab7_row25 :
    digitsEq 111 (rowProduct (ab6Rows 25) abRows 111) (ab7Rows 25)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem ab7_row26 :
    digitsEq 111 (rowProduct (ab6Rows 26) abRows 111) (ab7Rows 26)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem ab7_row27 :
    digitsEq 111 (rowProduct (ab6Rows 27) abRows 111) (ab7Rows 27)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem ab7_row28 :
    digitsEq 111 (rowProduct (ab6Rows 28) abRows 111) (ab7Rows 28)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem ab7_row29 :
    digitsEq 111 (rowProduct (ab6Rows 29) abRows 111) (ab7Rows 29)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem ab7_row30 :
    digitsEq 111 (rowProduct (ab6Rows 30) abRows 111) (ab7Rows 30)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem ab7_row31 :
    digitsEq 111 (rowProduct (ab6Rows 31) abRows 111) (ab7Rows 31)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem ab7_row32 :
    digitsEq 111 (rowProduct (ab6Rows 32) abRows 111) (ab7Rows 32)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem ab7_row33 :
    digitsEq 111 (rowProduct (ab6Rows 33) abRows 111) (ab7Rows 33)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem ab7_row34 :
    digitsEq 111 (rowProduct (ab6Rows 34) abRows 111) (ab7Rows 34)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem ab7_row35 :
    digitsEq 111 (rowProduct (ab6Rows 35) abRows 111) (ab7Rows 35)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem ab7_row36 :
    digitsEq 111 (rowProduct (ab6Rows 36) abRows 111) (ab7Rows 36)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem ab7_row37 :
    digitsEq 111 (rowProduct (ab6Rows 37) abRows 111) (ab7Rows 37)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem ab7_row38 :
    digitsEq 111 (rowProduct (ab6Rows 38) abRows 111) (ab7Rows 38)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem ab7_row39 :
    digitsEq 111 (rowProduct (ab6Rows 39) abRows 111) (ab7Rows 39)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem ab7_row40 :
    digitsEq 111 (rowProduct (ab6Rows 40) abRows 111) (ab7Rows 40)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem ab7_row41 :
    digitsEq 111 (rowProduct (ab6Rows 41) abRows 111) (ab7Rows 41)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem ab7_row42 :
    digitsEq 111 (rowProduct (ab6Rows 42) abRows 111) (ab7Rows 42)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem ab7_row43 :
    digitsEq 111 (rowProduct (ab6Rows 43) abRows 111) (ab7Rows 43)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem ab7_row44 :
    digitsEq 111 (rowProduct (ab6Rows 44) abRows 111) (ab7Rows 44)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem ab7_row45 :
    digitsEq 111 (rowProduct (ab6Rows 45) abRows 111) (ab7Rows 45)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem ab7_row46 :
    digitsEq 111 (rowProduct (ab6Rows 46) abRows 111) (ab7Rows 46)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem ab7_row47 :
    digitsEq 111 (rowProduct (ab6Rows 47) abRows 111) (ab7Rows 47)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem ab7_row48 :
    digitsEq 111 (rowProduct (ab6Rows 48) abRows 111) (ab7Rows 48)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem ab7_row49 :
    digitsEq 111 (rowProduct (ab6Rows 49) abRows 111) (ab7Rows 49)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem ab7_row50 :
    digitsEq 111 (rowProduct (ab6Rows 50) abRows 111) (ab7Rows 50)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem ab7_row51 :
    digitsEq 111 (rowProduct (ab6Rows 51) abRows 111) (ab7Rows 51)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem ab7_row52 :
    digitsEq 111 (rowProduct (ab6Rows 52) abRows 111) (ab7Rows 52)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem ab7_row53 :
    digitsEq 111 (rowProduct (ab6Rows 53) abRows 111) (ab7Rows 53)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem ab7_row54 :
    digitsEq 111 (rowProduct (ab6Rows 54) abRows 111) (ab7Rows 54)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem ab7_row55 :
    digitsEq 111 (rowProduct (ab6Rows 55) abRows 111) (ab7Rows 55)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem ab7_row56 :
    digitsEq 111 (rowProduct (ab6Rows 56) abRows 111) (ab7Rows 56)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem ab7_row57 :
    digitsEq 111 (rowProduct (ab6Rows 57) abRows 111) (ab7Rows 57)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem ab7_row58 :
    digitsEq 111 (rowProduct (ab6Rows 58) abRows 111) (ab7Rows 58)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem ab7_row59 :
    digitsEq 111 (rowProduct (ab6Rows 59) abRows 111) (ab7Rows 59)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem ab7_row60 :
    digitsEq 111 (rowProduct (ab6Rows 60) abRows 111) (ab7Rows 60)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem ab7_row61 :
    digitsEq 111 (rowProduct (ab6Rows 61) abRows 111) (ab7Rows 61)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem ab7_row62 :
    digitsEq 111 (rowProduct (ab6Rows 62) abRows 111) (ab7Rows 62)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem ab7_row63 :
    digitsEq 111 (rowProduct (ab6Rows 63) abRows 111) (ab7Rows 63)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem ab7_row64 :
    digitsEq 111 (rowProduct (ab6Rows 64) abRows 111) (ab7Rows 64)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem ab7_row65 :
    digitsEq 111 (rowProduct (ab6Rows 65) abRows 111) (ab7Rows 65)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem ab7_row66 :
    digitsEq 111 (rowProduct (ab6Rows 66) abRows 111) (ab7Rows 66)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem ab7_row67 :
    digitsEq 111 (rowProduct (ab6Rows 67) abRows 111) (ab7Rows 67)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem ab7_row68 :
    digitsEq 111 (rowProduct (ab6Rows 68) abRows 111) (ab7Rows 68)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem ab7_row69 :
    digitsEq 111 (rowProduct (ab6Rows 69) abRows 111) (ab7Rows 69)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem ab7_row70 :
    digitsEq 111 (rowProduct (ab6Rows 70) abRows 111) (ab7Rows 70)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem ab7_row71 :
    digitsEq 111 (rowProduct (ab6Rows 71) abRows 111) (ab7Rows 71)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem ab7_row72 :
    digitsEq 111 (rowProduct (ab6Rows 72) abRows 111) (ab7Rows 72)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem ab7_row73 :
    digitsEq 111 (rowProduct (ab6Rows 73) abRows 111) (ab7Rows 73)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem ab7_row74 :
    digitsEq 111 (rowProduct (ab6Rows 74) abRows 111) (ab7Rows 74)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem ab7_row75 :
    digitsEq 111 (rowProduct (ab6Rows 75) abRows 111) (ab7Rows 75)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem ab7_row76 :
    digitsEq 111 (rowProduct (ab6Rows 76) abRows 111) (ab7Rows 76)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem ab7_row77 :
    digitsEq 111 (rowProduct (ab6Rows 77) abRows 111) (ab7Rows 77)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem ab7_row78 :
    digitsEq 111 (rowProduct (ab6Rows 78) abRows 111) (ab7Rows 78)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem ab7_row79 :
    digitsEq 111 (rowProduct (ab6Rows 79) abRows 111) (ab7Rows 79)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem ab7_row80 :
    digitsEq 111 (rowProduct (ab6Rows 80) abRows 111) (ab7Rows 80)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem ab7_row81 :
    digitsEq 111 (rowProduct (ab6Rows 81) abRows 111) (ab7Rows 81)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem ab7_row82 :
    digitsEq 111 (rowProduct (ab6Rows 82) abRows 111) (ab7Rows 82)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem ab7_row83 :
    digitsEq 111 (rowProduct (ab6Rows 83) abRows 111) (ab7Rows 83)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem ab7_row84 :
    digitsEq 111 (rowProduct (ab6Rows 84) abRows 111) (ab7Rows 84)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem ab7_row85 :
    digitsEq 111 (rowProduct (ab6Rows 85) abRows 111) (ab7Rows 85)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem ab7_row86 :
    digitsEq 111 (rowProduct (ab6Rows 86) abRows 111) (ab7Rows 86)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem ab7_row87 :
    digitsEq 111 (rowProduct (ab6Rows 87) abRows 111) (ab7Rows 87)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem ab7_row88 :
    digitsEq 111 (rowProduct (ab6Rows 88) abRows 111) (ab7Rows 88)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem ab7_row89 :
    digitsEq 111 (rowProduct (ab6Rows 89) abRows 111) (ab7Rows 89)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem ab7_row90 :
    digitsEq 111 (rowProduct (ab6Rows 90) abRows 111) (ab7Rows 90)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem ab7_row91 :
    digitsEq 111 (rowProduct (ab6Rows 91) abRows 111) (ab7Rows 91)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem ab7_row92 :
    digitsEq 111 (rowProduct (ab6Rows 92) abRows 111) (ab7Rows 92)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem ab7_row93 :
    digitsEq 111 (rowProduct (ab6Rows 93) abRows 111) (ab7Rows 93)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem ab7_row94 :
    digitsEq 111 (rowProduct (ab6Rows 94) abRows 111) (ab7Rows 94)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem ab7_row95 :
    digitsEq 111 (rowProduct (ab6Rows 95) abRows 111) (ab7Rows 95)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem ab7_row96 :
    digitsEq 111 (rowProduct (ab6Rows 96) abRows 111) (ab7Rows 96)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem ab7_row97 :
    digitsEq 111 (rowProduct (ab6Rows 97) abRows 111) (ab7Rows 97)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem ab7_row98 :
    digitsEq 111 (rowProduct (ab6Rows 98) abRows 111) (ab7Rows 98)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem ab7_row99 :
    digitsEq 111 (rowProduct (ab6Rows 99) abRows 111) (ab7Rows 99)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem ab7_row100 :
    digitsEq 111 (rowProduct (ab6Rows 100) abRows 111) (ab7Rows 100)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem ab7_row101 :
    digitsEq 111 (rowProduct (ab6Rows 101) abRows 111) (ab7Rows 101)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem ab7_row102 :
    digitsEq 111 (rowProduct (ab6Rows 102) abRows 111) (ab7Rows 102)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem ab7_row103 :
    digitsEq 111 (rowProduct (ab6Rows 103) abRows 111) (ab7Rows 103)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem ab7_row104 :
    digitsEq 111 (rowProduct (ab6Rows 104) abRows 111) (ab7Rows 104)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem ab7_row105 :
    digitsEq 111 (rowProduct (ab6Rows 105) abRows 111) (ab7Rows 105)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem ab7_row106 :
    digitsEq 111 (rowProduct (ab6Rows 106) abRows 111) (ab7Rows 106)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem ab7_row107 :
    digitsEq 111 (rowProduct (ab6Rows 107) abRows 111) (ab7Rows 107)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem ab7_row108 :
    digitsEq 111 (rowProduct (ab6Rows 108) abRows 111) (ab7Rows 108)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem ab7_row109 :
    digitsEq 111 (rowProduct (ab6Rows 109) abRows 111) (ab7Rows 109)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem ab7_row110 :
    digitsEq 111 (rowProduct (ab6Rows 110) abRows 111) (ab7Rows 110)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem ab7_rows : ∀ i,
    digitsEq 111 (rowProduct (ab6Rows i) abRows 111) (ab7Rows i) = true :=
  (Fin.cases ab7_row0
    (Fin.cases ab7_row1
    (Fin.cases ab7_row2
    (Fin.cases ab7_row3
    (Fin.cases ab7_row4
    (Fin.cases ab7_row5
    (Fin.cases ab7_row6
    (Fin.cases ab7_row7
    (Fin.cases ab7_row8
    (Fin.cases ab7_row9
    (Fin.cases ab7_row10
    (Fin.cases ab7_row11
    (Fin.cases ab7_row12
    (Fin.cases ab7_row13
    (Fin.cases ab7_row14
    (Fin.cases ab7_row15
    (Fin.cases ab7_row16
    (Fin.cases ab7_row17
    (Fin.cases ab7_row18
    (Fin.cases ab7_row19
    (Fin.cases ab7_row20
    (Fin.cases ab7_row21
    (Fin.cases ab7_row22
    (Fin.cases ab7_row23
    (Fin.cases ab7_row24
    (Fin.cases ab7_row25
    (Fin.cases ab7_row26
    (Fin.cases ab7_row27
    (Fin.cases ab7_row28
    (Fin.cases ab7_row29
    (Fin.cases ab7_row30
    (Fin.cases ab7_row31
    (Fin.cases ab7_row32
    (Fin.cases ab7_row33
    (Fin.cases ab7_row34
    (Fin.cases ab7_row35
    (Fin.cases ab7_row36
    (Fin.cases ab7_row37
    (Fin.cases ab7_row38
    (Fin.cases ab7_row39
    (Fin.cases ab7_row40
    (Fin.cases ab7_row41
    (Fin.cases ab7_row42
    (Fin.cases ab7_row43
    (Fin.cases ab7_row44
    (Fin.cases ab7_row45
    (Fin.cases ab7_row46
    (Fin.cases ab7_row47
    (Fin.cases ab7_row48
    (Fin.cases ab7_row49
    (Fin.cases ab7_row50
    (Fin.cases ab7_row51
    (Fin.cases ab7_row52
    (Fin.cases ab7_row53
    (Fin.cases ab7_row54
    (Fin.cases ab7_row55
    (Fin.cases ab7_row56
    (Fin.cases ab7_row57
    (Fin.cases ab7_row58
    (Fin.cases ab7_row59
    (Fin.cases ab7_row60
    (Fin.cases ab7_row61
    (Fin.cases ab7_row62
    (Fin.cases ab7_row63
    (Fin.cases ab7_row64
    (Fin.cases ab7_row65
    (Fin.cases ab7_row66
    (Fin.cases ab7_row67
    (Fin.cases ab7_row68
    (Fin.cases ab7_row69
    (Fin.cases ab7_row70
    (Fin.cases ab7_row71
    (Fin.cases ab7_row72
    (Fin.cases ab7_row73
    (Fin.cases ab7_row74
    (Fin.cases ab7_row75
    (Fin.cases ab7_row76
    (Fin.cases ab7_row77
    (Fin.cases ab7_row78
    (Fin.cases ab7_row79
    (Fin.cases ab7_row80
    (Fin.cases ab7_row81
    (Fin.cases ab7_row82
    (Fin.cases ab7_row83
    (Fin.cases ab7_row84
    (Fin.cases ab7_row85
    (Fin.cases ab7_row86
    (Fin.cases ab7_row87
    (Fin.cases ab7_row88
    (Fin.cases ab7_row89
    (Fin.cases ab7_row90
    (Fin.cases ab7_row91
    (Fin.cases ab7_row92
    (Fin.cases ab7_row93
    (Fin.cases ab7_row94
    (Fin.cases ab7_row95
    (Fin.cases ab7_row96
    (Fin.cases ab7_row97
    (Fin.cases ab7_row98
    (Fin.cases ab7_row99
    (Fin.cases ab7_row100
    (Fin.cases ab7_row101
    (Fin.cases ab7_row102
    (Fin.cases ab7_row103
    (Fin.cases ab7_row104
    (Fin.cases ab7_row105
    (Fin.cases ab7_row106
    (Fin.cases ab7_row107
    (Fin.cases ab7_row108
    (Fin.cases ab7_row109
    (Fin.cases ab7_row110
    (fun i => Fin.elim0 i))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

/-- Checked multiplication in the actual matrix algebra. -/
public theorem mul_ab7 : ab6Matrix * abMatrix = ab7Matrix :=
  decode_mul _ _ _ ab6_small ab_small ab7_rows

end Lyons.Atlas111WordCertificate
