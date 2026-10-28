module

public import Theory.SpecificGroups.Lyons.Atlas111WordRelations.Data

/-!
# Certified Lyons multiplication: w66 times w

These 111 row checks certify `w66Matrix * wMatrix = oneMatrix`.
The carry-free arithmetic soundness theorem gives the matrix identity.
Source: `../Atlas111Source/` and `../Atlas111WordSource/Generate.py`.
All closed certificates are checked by the Lean kernel.
-/

namespace Lyons.Atlas111WordCertificate

set_option Elab.async false

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w67_row0 :
    digitsEq 111 (rowProduct (w66Rows 0) wRows 111) (oneRows 0)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w67_row1 :
    digitsEq 111 (rowProduct (w66Rows 1) wRows 111) (oneRows 1)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w67_row2 :
    digitsEq 111 (rowProduct (w66Rows 2) wRows 111) (oneRows 2)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w67_row3 :
    digitsEq 111 (rowProduct (w66Rows 3) wRows 111) (oneRows 3)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w67_row4 :
    digitsEq 111 (rowProduct (w66Rows 4) wRows 111) (oneRows 4)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w67_row5 :
    digitsEq 111 (rowProduct (w66Rows 5) wRows 111) (oneRows 5)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w67_row6 :
    digitsEq 111 (rowProduct (w66Rows 6) wRows 111) (oneRows 6)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w67_row7 :
    digitsEq 111 (rowProduct (w66Rows 7) wRows 111) (oneRows 7)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w67_row8 :
    digitsEq 111 (rowProduct (w66Rows 8) wRows 111) (oneRows 8)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w67_row9 :
    digitsEq 111 (rowProduct (w66Rows 9) wRows 111) (oneRows 9)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w67_row10 :
    digitsEq 111 (rowProduct (w66Rows 10) wRows 111) (oneRows 10)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w67_row11 :
    digitsEq 111 (rowProduct (w66Rows 11) wRows 111) (oneRows 11)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w67_row12 :
    digitsEq 111 (rowProduct (w66Rows 12) wRows 111) (oneRows 12)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w67_row13 :
    digitsEq 111 (rowProduct (w66Rows 13) wRows 111) (oneRows 13)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w67_row14 :
    digitsEq 111 (rowProduct (w66Rows 14) wRows 111) (oneRows 14)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w67_row15 :
    digitsEq 111 (rowProduct (w66Rows 15) wRows 111) (oneRows 15)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w67_row16 :
    digitsEq 111 (rowProduct (w66Rows 16) wRows 111) (oneRows 16)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w67_row17 :
    digitsEq 111 (rowProduct (w66Rows 17) wRows 111) (oneRows 17)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w67_row18 :
    digitsEq 111 (rowProduct (w66Rows 18) wRows 111) (oneRows 18)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w67_row19 :
    digitsEq 111 (rowProduct (w66Rows 19) wRows 111) (oneRows 19)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w67_row20 :
    digitsEq 111 (rowProduct (w66Rows 20) wRows 111) (oneRows 20)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w67_row21 :
    digitsEq 111 (rowProduct (w66Rows 21) wRows 111) (oneRows 21)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w67_row22 :
    digitsEq 111 (rowProduct (w66Rows 22) wRows 111) (oneRows 22)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w67_row23 :
    digitsEq 111 (rowProduct (w66Rows 23) wRows 111) (oneRows 23)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w67_row24 :
    digitsEq 111 (rowProduct (w66Rows 24) wRows 111) (oneRows 24)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w67_row25 :
    digitsEq 111 (rowProduct (w66Rows 25) wRows 111) (oneRows 25)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w67_row26 :
    digitsEq 111 (rowProduct (w66Rows 26) wRows 111) (oneRows 26)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w67_row27 :
    digitsEq 111 (rowProduct (w66Rows 27) wRows 111) (oneRows 27)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w67_row28 :
    digitsEq 111 (rowProduct (w66Rows 28) wRows 111) (oneRows 28)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w67_row29 :
    digitsEq 111 (rowProduct (w66Rows 29) wRows 111) (oneRows 29)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w67_row30 :
    digitsEq 111 (rowProduct (w66Rows 30) wRows 111) (oneRows 30)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w67_row31 :
    digitsEq 111 (rowProduct (w66Rows 31) wRows 111) (oneRows 31)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w67_row32 :
    digitsEq 111 (rowProduct (w66Rows 32) wRows 111) (oneRows 32)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w67_row33 :
    digitsEq 111 (rowProduct (w66Rows 33) wRows 111) (oneRows 33)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w67_row34 :
    digitsEq 111 (rowProduct (w66Rows 34) wRows 111) (oneRows 34)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w67_row35 :
    digitsEq 111 (rowProduct (w66Rows 35) wRows 111) (oneRows 35)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w67_row36 :
    digitsEq 111 (rowProduct (w66Rows 36) wRows 111) (oneRows 36)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w67_row37 :
    digitsEq 111 (rowProduct (w66Rows 37) wRows 111) (oneRows 37)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w67_row38 :
    digitsEq 111 (rowProduct (w66Rows 38) wRows 111) (oneRows 38)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w67_row39 :
    digitsEq 111 (rowProduct (w66Rows 39) wRows 111) (oneRows 39)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w67_row40 :
    digitsEq 111 (rowProduct (w66Rows 40) wRows 111) (oneRows 40)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w67_row41 :
    digitsEq 111 (rowProduct (w66Rows 41) wRows 111) (oneRows 41)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w67_row42 :
    digitsEq 111 (rowProduct (w66Rows 42) wRows 111) (oneRows 42)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w67_row43 :
    digitsEq 111 (rowProduct (w66Rows 43) wRows 111) (oneRows 43)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w67_row44 :
    digitsEq 111 (rowProduct (w66Rows 44) wRows 111) (oneRows 44)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w67_row45 :
    digitsEq 111 (rowProduct (w66Rows 45) wRows 111) (oneRows 45)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w67_row46 :
    digitsEq 111 (rowProduct (w66Rows 46) wRows 111) (oneRows 46)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w67_row47 :
    digitsEq 111 (rowProduct (w66Rows 47) wRows 111) (oneRows 47)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w67_row48 :
    digitsEq 111 (rowProduct (w66Rows 48) wRows 111) (oneRows 48)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w67_row49 :
    digitsEq 111 (rowProduct (w66Rows 49) wRows 111) (oneRows 49)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w67_row50 :
    digitsEq 111 (rowProduct (w66Rows 50) wRows 111) (oneRows 50)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w67_row51 :
    digitsEq 111 (rowProduct (w66Rows 51) wRows 111) (oneRows 51)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w67_row52 :
    digitsEq 111 (rowProduct (w66Rows 52) wRows 111) (oneRows 52)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w67_row53 :
    digitsEq 111 (rowProduct (w66Rows 53) wRows 111) (oneRows 53)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w67_row54 :
    digitsEq 111 (rowProduct (w66Rows 54) wRows 111) (oneRows 54)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w67_row55 :
    digitsEq 111 (rowProduct (w66Rows 55) wRows 111) (oneRows 55)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w67_row56 :
    digitsEq 111 (rowProduct (w66Rows 56) wRows 111) (oneRows 56)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w67_row57 :
    digitsEq 111 (rowProduct (w66Rows 57) wRows 111) (oneRows 57)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w67_row58 :
    digitsEq 111 (rowProduct (w66Rows 58) wRows 111) (oneRows 58)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w67_row59 :
    digitsEq 111 (rowProduct (w66Rows 59) wRows 111) (oneRows 59)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w67_row60 :
    digitsEq 111 (rowProduct (w66Rows 60) wRows 111) (oneRows 60)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w67_row61 :
    digitsEq 111 (rowProduct (w66Rows 61) wRows 111) (oneRows 61)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w67_row62 :
    digitsEq 111 (rowProduct (w66Rows 62) wRows 111) (oneRows 62)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w67_row63 :
    digitsEq 111 (rowProduct (w66Rows 63) wRows 111) (oneRows 63)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w67_row64 :
    digitsEq 111 (rowProduct (w66Rows 64) wRows 111) (oneRows 64)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w67_row65 :
    digitsEq 111 (rowProduct (w66Rows 65) wRows 111) (oneRows 65)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w67_row66 :
    digitsEq 111 (rowProduct (w66Rows 66) wRows 111) (oneRows 66)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w67_row67 :
    digitsEq 111 (rowProduct (w66Rows 67) wRows 111) (oneRows 67)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w67_row68 :
    digitsEq 111 (rowProduct (w66Rows 68) wRows 111) (oneRows 68)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w67_row69 :
    digitsEq 111 (rowProduct (w66Rows 69) wRows 111) (oneRows 69)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w67_row70 :
    digitsEq 111 (rowProduct (w66Rows 70) wRows 111) (oneRows 70)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w67_row71 :
    digitsEq 111 (rowProduct (w66Rows 71) wRows 111) (oneRows 71)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w67_row72 :
    digitsEq 111 (rowProduct (w66Rows 72) wRows 111) (oneRows 72)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w67_row73 :
    digitsEq 111 (rowProduct (w66Rows 73) wRows 111) (oneRows 73)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w67_row74 :
    digitsEq 111 (rowProduct (w66Rows 74) wRows 111) (oneRows 74)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w67_row75 :
    digitsEq 111 (rowProduct (w66Rows 75) wRows 111) (oneRows 75)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w67_row76 :
    digitsEq 111 (rowProduct (w66Rows 76) wRows 111) (oneRows 76)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w67_row77 :
    digitsEq 111 (rowProduct (w66Rows 77) wRows 111) (oneRows 77)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w67_row78 :
    digitsEq 111 (rowProduct (w66Rows 78) wRows 111) (oneRows 78)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w67_row79 :
    digitsEq 111 (rowProduct (w66Rows 79) wRows 111) (oneRows 79)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w67_row80 :
    digitsEq 111 (rowProduct (w66Rows 80) wRows 111) (oneRows 80)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w67_row81 :
    digitsEq 111 (rowProduct (w66Rows 81) wRows 111) (oneRows 81)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w67_row82 :
    digitsEq 111 (rowProduct (w66Rows 82) wRows 111) (oneRows 82)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w67_row83 :
    digitsEq 111 (rowProduct (w66Rows 83) wRows 111) (oneRows 83)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w67_row84 :
    digitsEq 111 (rowProduct (w66Rows 84) wRows 111) (oneRows 84)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w67_row85 :
    digitsEq 111 (rowProduct (w66Rows 85) wRows 111) (oneRows 85)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w67_row86 :
    digitsEq 111 (rowProduct (w66Rows 86) wRows 111) (oneRows 86)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w67_row87 :
    digitsEq 111 (rowProduct (w66Rows 87) wRows 111) (oneRows 87)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w67_row88 :
    digitsEq 111 (rowProduct (w66Rows 88) wRows 111) (oneRows 88)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w67_row89 :
    digitsEq 111 (rowProduct (w66Rows 89) wRows 111) (oneRows 89)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w67_row90 :
    digitsEq 111 (rowProduct (w66Rows 90) wRows 111) (oneRows 90)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w67_row91 :
    digitsEq 111 (rowProduct (w66Rows 91) wRows 111) (oneRows 91)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w67_row92 :
    digitsEq 111 (rowProduct (w66Rows 92) wRows 111) (oneRows 92)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w67_row93 :
    digitsEq 111 (rowProduct (w66Rows 93) wRows 111) (oneRows 93)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w67_row94 :
    digitsEq 111 (rowProduct (w66Rows 94) wRows 111) (oneRows 94)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w67_row95 :
    digitsEq 111 (rowProduct (w66Rows 95) wRows 111) (oneRows 95)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w67_row96 :
    digitsEq 111 (rowProduct (w66Rows 96) wRows 111) (oneRows 96)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w67_row97 :
    digitsEq 111 (rowProduct (w66Rows 97) wRows 111) (oneRows 97)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w67_row98 :
    digitsEq 111 (rowProduct (w66Rows 98) wRows 111) (oneRows 98)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w67_row99 :
    digitsEq 111 (rowProduct (w66Rows 99) wRows 111) (oneRows 99)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w67_row100 :
    digitsEq 111 (rowProduct (w66Rows 100) wRows 111) (oneRows 100)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w67_row101 :
    digitsEq 111 (rowProduct (w66Rows 101) wRows 111) (oneRows 101)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w67_row102 :
    digitsEq 111 (rowProduct (w66Rows 102) wRows 111) (oneRows 102)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w67_row103 :
    digitsEq 111 (rowProduct (w66Rows 103) wRows 111) (oneRows 103)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w67_row104 :
    digitsEq 111 (rowProduct (w66Rows 104) wRows 111) (oneRows 104)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w67_row105 :
    digitsEq 111 (rowProduct (w66Rows 105) wRows 111) (oneRows 105)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w67_row106 :
    digitsEq 111 (rowProduct (w66Rows 106) wRows 111) (oneRows 106)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w67_row107 :
    digitsEq 111 (rowProduct (w66Rows 107) wRows 111) (oneRows 107)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w67_row108 :
    digitsEq 111 (rowProduct (w66Rows 108) wRows 111) (oneRows 108)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w67_row109 :
    digitsEq 111 (rowProduct (w66Rows 109) wRows 111) (oneRows 109)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w67_row110 :
    digitsEq 111 (rowProduct (w66Rows 110) wRows 111) (oneRows 110)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem w67_rows : ∀ i,
    digitsEq 111 (rowProduct (w66Rows i) wRows 111) (oneRows i) = true :=
  (Fin.cases w67_row0
    (Fin.cases w67_row1
    (Fin.cases w67_row2
    (Fin.cases w67_row3
    (Fin.cases w67_row4
    (Fin.cases w67_row5
    (Fin.cases w67_row6
    (Fin.cases w67_row7
    (Fin.cases w67_row8
    (Fin.cases w67_row9
    (Fin.cases w67_row10
    (Fin.cases w67_row11
    (Fin.cases w67_row12
    (Fin.cases w67_row13
    (Fin.cases w67_row14
    (Fin.cases w67_row15
    (Fin.cases w67_row16
    (Fin.cases w67_row17
    (Fin.cases w67_row18
    (Fin.cases w67_row19
    (Fin.cases w67_row20
    (Fin.cases w67_row21
    (Fin.cases w67_row22
    (Fin.cases w67_row23
    (Fin.cases w67_row24
    (Fin.cases w67_row25
    (Fin.cases w67_row26
    (Fin.cases w67_row27
    (Fin.cases w67_row28
    (Fin.cases w67_row29
    (Fin.cases w67_row30
    (Fin.cases w67_row31
    (Fin.cases w67_row32
    (Fin.cases w67_row33
    (Fin.cases w67_row34
    (Fin.cases w67_row35
    (Fin.cases w67_row36
    (Fin.cases w67_row37
    (Fin.cases w67_row38
    (Fin.cases w67_row39
    (Fin.cases w67_row40
    (Fin.cases w67_row41
    (Fin.cases w67_row42
    (Fin.cases w67_row43
    (Fin.cases w67_row44
    (Fin.cases w67_row45
    (Fin.cases w67_row46
    (Fin.cases w67_row47
    (Fin.cases w67_row48
    (Fin.cases w67_row49
    (Fin.cases w67_row50
    (Fin.cases w67_row51
    (Fin.cases w67_row52
    (Fin.cases w67_row53
    (Fin.cases w67_row54
    (Fin.cases w67_row55
    (Fin.cases w67_row56
    (Fin.cases w67_row57
    (Fin.cases w67_row58
    (Fin.cases w67_row59
    (Fin.cases w67_row60
    (Fin.cases w67_row61
    (Fin.cases w67_row62
    (Fin.cases w67_row63
    (Fin.cases w67_row64
    (Fin.cases w67_row65
    (Fin.cases w67_row66
    (Fin.cases w67_row67
    (Fin.cases w67_row68
    (Fin.cases w67_row69
    (Fin.cases w67_row70
    (Fin.cases w67_row71
    (Fin.cases w67_row72
    (Fin.cases w67_row73
    (Fin.cases w67_row74
    (Fin.cases w67_row75
    (Fin.cases w67_row76
    (Fin.cases w67_row77
    (Fin.cases w67_row78
    (Fin.cases w67_row79
    (Fin.cases w67_row80
    (Fin.cases w67_row81
    (Fin.cases w67_row82
    (Fin.cases w67_row83
    (Fin.cases w67_row84
    (Fin.cases w67_row85
    (Fin.cases w67_row86
    (Fin.cases w67_row87
    (Fin.cases w67_row88
    (Fin.cases w67_row89
    (Fin.cases w67_row90
    (Fin.cases w67_row91
    (Fin.cases w67_row92
    (Fin.cases w67_row93
    (Fin.cases w67_row94
    (Fin.cases w67_row95
    (Fin.cases w67_row96
    (Fin.cases w67_row97
    (Fin.cases w67_row98
    (Fin.cases w67_row99
    (Fin.cases w67_row100
    (Fin.cases w67_row101
    (Fin.cases w67_row102
    (Fin.cases w67_row103
    (Fin.cases w67_row104
    (Fin.cases w67_row105
    (Fin.cases w67_row106
    (Fin.cases w67_row107
    (Fin.cases w67_row108
    (Fin.cases w67_row109
    (Fin.cases w67_row110
    (fun i => Fin.elim0 i))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

/-- Checked multiplication in the actual matrix algebra. -/
public theorem mul_w67 : w66Matrix * wMatrix = oneMatrix :=
  decode_mul _ _ _ w66_small w_small w67_rows

end Lyons.Atlas111WordCertificate
