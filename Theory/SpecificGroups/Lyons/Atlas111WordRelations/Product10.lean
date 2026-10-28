module

public import Theory.SpecificGroups.Lyons.Atlas111WordRelations.Data

/-!
# Certified Lyons multiplication: w times w

These 111 row checks certify `wMatrix * wMatrix = w2Matrix`.
The carry-free arithmetic soundness theorem gives the matrix identity.
Source: `../Atlas111Source/` and `../Atlas111WordSource/Generate.py`.
All closed certificates are checked by the Lean kernel.
-/

namespace Lyons.Atlas111WordCertificate

set_option Elab.async false

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w2_row0 :
    digitsEq 111 (rowProduct (wRows 0) wRows 111) (w2Rows 0)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w2_row1 :
    digitsEq 111 (rowProduct (wRows 1) wRows 111) (w2Rows 1)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w2_row2 :
    digitsEq 111 (rowProduct (wRows 2) wRows 111) (w2Rows 2)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w2_row3 :
    digitsEq 111 (rowProduct (wRows 3) wRows 111) (w2Rows 3)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w2_row4 :
    digitsEq 111 (rowProduct (wRows 4) wRows 111) (w2Rows 4)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w2_row5 :
    digitsEq 111 (rowProduct (wRows 5) wRows 111) (w2Rows 5)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w2_row6 :
    digitsEq 111 (rowProduct (wRows 6) wRows 111) (w2Rows 6)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w2_row7 :
    digitsEq 111 (rowProduct (wRows 7) wRows 111) (w2Rows 7)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w2_row8 :
    digitsEq 111 (rowProduct (wRows 8) wRows 111) (w2Rows 8)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w2_row9 :
    digitsEq 111 (rowProduct (wRows 9) wRows 111) (w2Rows 9)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w2_row10 :
    digitsEq 111 (rowProduct (wRows 10) wRows 111) (w2Rows 10)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w2_row11 :
    digitsEq 111 (rowProduct (wRows 11) wRows 111) (w2Rows 11)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w2_row12 :
    digitsEq 111 (rowProduct (wRows 12) wRows 111) (w2Rows 12)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w2_row13 :
    digitsEq 111 (rowProduct (wRows 13) wRows 111) (w2Rows 13)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w2_row14 :
    digitsEq 111 (rowProduct (wRows 14) wRows 111) (w2Rows 14)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w2_row15 :
    digitsEq 111 (rowProduct (wRows 15) wRows 111) (w2Rows 15)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w2_row16 :
    digitsEq 111 (rowProduct (wRows 16) wRows 111) (w2Rows 16)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w2_row17 :
    digitsEq 111 (rowProduct (wRows 17) wRows 111) (w2Rows 17)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w2_row18 :
    digitsEq 111 (rowProduct (wRows 18) wRows 111) (w2Rows 18)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w2_row19 :
    digitsEq 111 (rowProduct (wRows 19) wRows 111) (w2Rows 19)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w2_row20 :
    digitsEq 111 (rowProduct (wRows 20) wRows 111) (w2Rows 20)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w2_row21 :
    digitsEq 111 (rowProduct (wRows 21) wRows 111) (w2Rows 21)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w2_row22 :
    digitsEq 111 (rowProduct (wRows 22) wRows 111) (w2Rows 22)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w2_row23 :
    digitsEq 111 (rowProduct (wRows 23) wRows 111) (w2Rows 23)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w2_row24 :
    digitsEq 111 (rowProduct (wRows 24) wRows 111) (w2Rows 24)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w2_row25 :
    digitsEq 111 (rowProduct (wRows 25) wRows 111) (w2Rows 25)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w2_row26 :
    digitsEq 111 (rowProduct (wRows 26) wRows 111) (w2Rows 26)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w2_row27 :
    digitsEq 111 (rowProduct (wRows 27) wRows 111) (w2Rows 27)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w2_row28 :
    digitsEq 111 (rowProduct (wRows 28) wRows 111) (w2Rows 28)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w2_row29 :
    digitsEq 111 (rowProduct (wRows 29) wRows 111) (w2Rows 29)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w2_row30 :
    digitsEq 111 (rowProduct (wRows 30) wRows 111) (w2Rows 30)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w2_row31 :
    digitsEq 111 (rowProduct (wRows 31) wRows 111) (w2Rows 31)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w2_row32 :
    digitsEq 111 (rowProduct (wRows 32) wRows 111) (w2Rows 32)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w2_row33 :
    digitsEq 111 (rowProduct (wRows 33) wRows 111) (w2Rows 33)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w2_row34 :
    digitsEq 111 (rowProduct (wRows 34) wRows 111) (w2Rows 34)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w2_row35 :
    digitsEq 111 (rowProduct (wRows 35) wRows 111) (w2Rows 35)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w2_row36 :
    digitsEq 111 (rowProduct (wRows 36) wRows 111) (w2Rows 36)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w2_row37 :
    digitsEq 111 (rowProduct (wRows 37) wRows 111) (w2Rows 37)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w2_row38 :
    digitsEq 111 (rowProduct (wRows 38) wRows 111) (w2Rows 38)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w2_row39 :
    digitsEq 111 (rowProduct (wRows 39) wRows 111) (w2Rows 39)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w2_row40 :
    digitsEq 111 (rowProduct (wRows 40) wRows 111) (w2Rows 40)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w2_row41 :
    digitsEq 111 (rowProduct (wRows 41) wRows 111) (w2Rows 41)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w2_row42 :
    digitsEq 111 (rowProduct (wRows 42) wRows 111) (w2Rows 42)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w2_row43 :
    digitsEq 111 (rowProduct (wRows 43) wRows 111) (w2Rows 43)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w2_row44 :
    digitsEq 111 (rowProduct (wRows 44) wRows 111) (w2Rows 44)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w2_row45 :
    digitsEq 111 (rowProduct (wRows 45) wRows 111) (w2Rows 45)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w2_row46 :
    digitsEq 111 (rowProduct (wRows 46) wRows 111) (w2Rows 46)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w2_row47 :
    digitsEq 111 (rowProduct (wRows 47) wRows 111) (w2Rows 47)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w2_row48 :
    digitsEq 111 (rowProduct (wRows 48) wRows 111) (w2Rows 48)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w2_row49 :
    digitsEq 111 (rowProduct (wRows 49) wRows 111) (w2Rows 49)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w2_row50 :
    digitsEq 111 (rowProduct (wRows 50) wRows 111) (w2Rows 50)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w2_row51 :
    digitsEq 111 (rowProduct (wRows 51) wRows 111) (w2Rows 51)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w2_row52 :
    digitsEq 111 (rowProduct (wRows 52) wRows 111) (w2Rows 52)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w2_row53 :
    digitsEq 111 (rowProduct (wRows 53) wRows 111) (w2Rows 53)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w2_row54 :
    digitsEq 111 (rowProduct (wRows 54) wRows 111) (w2Rows 54)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w2_row55 :
    digitsEq 111 (rowProduct (wRows 55) wRows 111) (w2Rows 55)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w2_row56 :
    digitsEq 111 (rowProduct (wRows 56) wRows 111) (w2Rows 56)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w2_row57 :
    digitsEq 111 (rowProduct (wRows 57) wRows 111) (w2Rows 57)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w2_row58 :
    digitsEq 111 (rowProduct (wRows 58) wRows 111) (w2Rows 58)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w2_row59 :
    digitsEq 111 (rowProduct (wRows 59) wRows 111) (w2Rows 59)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w2_row60 :
    digitsEq 111 (rowProduct (wRows 60) wRows 111) (w2Rows 60)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w2_row61 :
    digitsEq 111 (rowProduct (wRows 61) wRows 111) (w2Rows 61)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w2_row62 :
    digitsEq 111 (rowProduct (wRows 62) wRows 111) (w2Rows 62)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w2_row63 :
    digitsEq 111 (rowProduct (wRows 63) wRows 111) (w2Rows 63)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w2_row64 :
    digitsEq 111 (rowProduct (wRows 64) wRows 111) (w2Rows 64)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w2_row65 :
    digitsEq 111 (rowProduct (wRows 65) wRows 111) (w2Rows 65)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w2_row66 :
    digitsEq 111 (rowProduct (wRows 66) wRows 111) (w2Rows 66)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w2_row67 :
    digitsEq 111 (rowProduct (wRows 67) wRows 111) (w2Rows 67)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w2_row68 :
    digitsEq 111 (rowProduct (wRows 68) wRows 111) (w2Rows 68)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w2_row69 :
    digitsEq 111 (rowProduct (wRows 69) wRows 111) (w2Rows 69)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w2_row70 :
    digitsEq 111 (rowProduct (wRows 70) wRows 111) (w2Rows 70)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w2_row71 :
    digitsEq 111 (rowProduct (wRows 71) wRows 111) (w2Rows 71)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w2_row72 :
    digitsEq 111 (rowProduct (wRows 72) wRows 111) (w2Rows 72)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w2_row73 :
    digitsEq 111 (rowProduct (wRows 73) wRows 111) (w2Rows 73)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w2_row74 :
    digitsEq 111 (rowProduct (wRows 74) wRows 111) (w2Rows 74)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w2_row75 :
    digitsEq 111 (rowProduct (wRows 75) wRows 111) (w2Rows 75)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w2_row76 :
    digitsEq 111 (rowProduct (wRows 76) wRows 111) (w2Rows 76)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w2_row77 :
    digitsEq 111 (rowProduct (wRows 77) wRows 111) (w2Rows 77)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w2_row78 :
    digitsEq 111 (rowProduct (wRows 78) wRows 111) (w2Rows 78)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w2_row79 :
    digitsEq 111 (rowProduct (wRows 79) wRows 111) (w2Rows 79)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w2_row80 :
    digitsEq 111 (rowProduct (wRows 80) wRows 111) (w2Rows 80)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w2_row81 :
    digitsEq 111 (rowProduct (wRows 81) wRows 111) (w2Rows 81)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w2_row82 :
    digitsEq 111 (rowProduct (wRows 82) wRows 111) (w2Rows 82)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w2_row83 :
    digitsEq 111 (rowProduct (wRows 83) wRows 111) (w2Rows 83)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w2_row84 :
    digitsEq 111 (rowProduct (wRows 84) wRows 111) (w2Rows 84)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w2_row85 :
    digitsEq 111 (rowProduct (wRows 85) wRows 111) (w2Rows 85)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w2_row86 :
    digitsEq 111 (rowProduct (wRows 86) wRows 111) (w2Rows 86)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w2_row87 :
    digitsEq 111 (rowProduct (wRows 87) wRows 111) (w2Rows 87)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w2_row88 :
    digitsEq 111 (rowProduct (wRows 88) wRows 111) (w2Rows 88)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w2_row89 :
    digitsEq 111 (rowProduct (wRows 89) wRows 111) (w2Rows 89)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w2_row90 :
    digitsEq 111 (rowProduct (wRows 90) wRows 111) (w2Rows 90)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w2_row91 :
    digitsEq 111 (rowProduct (wRows 91) wRows 111) (w2Rows 91)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w2_row92 :
    digitsEq 111 (rowProduct (wRows 92) wRows 111) (w2Rows 92)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w2_row93 :
    digitsEq 111 (rowProduct (wRows 93) wRows 111) (w2Rows 93)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w2_row94 :
    digitsEq 111 (rowProduct (wRows 94) wRows 111) (w2Rows 94)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w2_row95 :
    digitsEq 111 (rowProduct (wRows 95) wRows 111) (w2Rows 95)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w2_row96 :
    digitsEq 111 (rowProduct (wRows 96) wRows 111) (w2Rows 96)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w2_row97 :
    digitsEq 111 (rowProduct (wRows 97) wRows 111) (w2Rows 97)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w2_row98 :
    digitsEq 111 (rowProduct (wRows 98) wRows 111) (w2Rows 98)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w2_row99 :
    digitsEq 111 (rowProduct (wRows 99) wRows 111) (w2Rows 99)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w2_row100 :
    digitsEq 111 (rowProduct (wRows 100) wRows 111) (w2Rows 100)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w2_row101 :
    digitsEq 111 (rowProduct (wRows 101) wRows 111) (w2Rows 101)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w2_row102 :
    digitsEq 111 (rowProduct (wRows 102) wRows 111) (w2Rows 102)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w2_row103 :
    digitsEq 111 (rowProduct (wRows 103) wRows 111) (w2Rows 103)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w2_row104 :
    digitsEq 111 (rowProduct (wRows 104) wRows 111) (w2Rows 104)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w2_row105 :
    digitsEq 111 (rowProduct (wRows 105) wRows 111) (w2Rows 105)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w2_row106 :
    digitsEq 111 (rowProduct (wRows 106) wRows 111) (w2Rows 106)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w2_row107 :
    digitsEq 111 (rowProduct (wRows 107) wRows 111) (w2Rows 107)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w2_row108 :
    digitsEq 111 (rowProduct (wRows 108) wRows 111) (w2Rows 108)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w2_row109 :
    digitsEq 111 (rowProduct (wRows 109) wRows 111) (w2Rows 109)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w2_row110 :
    digitsEq 111 (rowProduct (wRows 110) wRows 111) (w2Rows 110)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem w2_rows : ∀ i,
    digitsEq 111 (rowProduct (wRows i) wRows 111) (w2Rows i) = true :=
  (Fin.cases w2_row0
    (Fin.cases w2_row1
    (Fin.cases w2_row2
    (Fin.cases w2_row3
    (Fin.cases w2_row4
    (Fin.cases w2_row5
    (Fin.cases w2_row6
    (Fin.cases w2_row7
    (Fin.cases w2_row8
    (Fin.cases w2_row9
    (Fin.cases w2_row10
    (Fin.cases w2_row11
    (Fin.cases w2_row12
    (Fin.cases w2_row13
    (Fin.cases w2_row14
    (Fin.cases w2_row15
    (Fin.cases w2_row16
    (Fin.cases w2_row17
    (Fin.cases w2_row18
    (Fin.cases w2_row19
    (Fin.cases w2_row20
    (Fin.cases w2_row21
    (Fin.cases w2_row22
    (Fin.cases w2_row23
    (Fin.cases w2_row24
    (Fin.cases w2_row25
    (Fin.cases w2_row26
    (Fin.cases w2_row27
    (Fin.cases w2_row28
    (Fin.cases w2_row29
    (Fin.cases w2_row30
    (Fin.cases w2_row31
    (Fin.cases w2_row32
    (Fin.cases w2_row33
    (Fin.cases w2_row34
    (Fin.cases w2_row35
    (Fin.cases w2_row36
    (Fin.cases w2_row37
    (Fin.cases w2_row38
    (Fin.cases w2_row39
    (Fin.cases w2_row40
    (Fin.cases w2_row41
    (Fin.cases w2_row42
    (Fin.cases w2_row43
    (Fin.cases w2_row44
    (Fin.cases w2_row45
    (Fin.cases w2_row46
    (Fin.cases w2_row47
    (Fin.cases w2_row48
    (Fin.cases w2_row49
    (Fin.cases w2_row50
    (Fin.cases w2_row51
    (Fin.cases w2_row52
    (Fin.cases w2_row53
    (Fin.cases w2_row54
    (Fin.cases w2_row55
    (Fin.cases w2_row56
    (Fin.cases w2_row57
    (Fin.cases w2_row58
    (Fin.cases w2_row59
    (Fin.cases w2_row60
    (Fin.cases w2_row61
    (Fin.cases w2_row62
    (Fin.cases w2_row63
    (Fin.cases w2_row64
    (Fin.cases w2_row65
    (Fin.cases w2_row66
    (Fin.cases w2_row67
    (Fin.cases w2_row68
    (Fin.cases w2_row69
    (Fin.cases w2_row70
    (Fin.cases w2_row71
    (Fin.cases w2_row72
    (Fin.cases w2_row73
    (Fin.cases w2_row74
    (Fin.cases w2_row75
    (Fin.cases w2_row76
    (Fin.cases w2_row77
    (Fin.cases w2_row78
    (Fin.cases w2_row79
    (Fin.cases w2_row80
    (Fin.cases w2_row81
    (Fin.cases w2_row82
    (Fin.cases w2_row83
    (Fin.cases w2_row84
    (Fin.cases w2_row85
    (Fin.cases w2_row86
    (Fin.cases w2_row87
    (Fin.cases w2_row88
    (Fin.cases w2_row89
    (Fin.cases w2_row90
    (Fin.cases w2_row91
    (Fin.cases w2_row92
    (Fin.cases w2_row93
    (Fin.cases w2_row94
    (Fin.cases w2_row95
    (Fin.cases w2_row96
    (Fin.cases w2_row97
    (Fin.cases w2_row98
    (Fin.cases w2_row99
    (Fin.cases w2_row100
    (Fin.cases w2_row101
    (Fin.cases w2_row102
    (Fin.cases w2_row103
    (Fin.cases w2_row104
    (Fin.cases w2_row105
    (Fin.cases w2_row106
    (Fin.cases w2_row107
    (Fin.cases w2_row108
    (Fin.cases w2_row109
    (Fin.cases w2_row110
    (fun i => Fin.elim0 i))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

/-- Checked multiplication in the actual matrix algebra. -/
public theorem mul_w2 : wMatrix * wMatrix = w2Matrix :=
  decode_mul _ _ _ w_small w_small w2_rows

end Lyons.Atlas111WordCertificate
